from idaapi import *

def forall_funcs():
    fn = get_next_func(0)
    while fn is not None:
        yield fn
        fn = get_next_func(fn.start_ea)

def is_code_at(ea):
    return is_code(get_flags(ea))

def forall_insns_in_range( start, end):
    ea = start
    while ea < end:
        if not is_code_at(ea):
            ea += 1
            continue

        insn = insn_t()
        decode_insn(insn, ea)
        yield insn
        ea = ea + insn.size

def forall_insns_in_func(fn):
    for insn in forall_insns_in_range(fn.start_ea, fn.end_ea):
        yield insn

NOPTABLE_impl = [
    [0x90],
    [0x66, 0x90],
    [0x0F,0x1F,0x00] ,
    [0x0F, 0x1F, 0x40, 0x00],
    [0x0F, 0x1F, 0x44, 0x00, 0x00],
    [0x66, 0x0F, 0x1F, 0x44,  0x00, 0x00],
    [0x0F, 0x1F, 0x80, 0x00, 0x00, 0x00, 0x00],
    [0x0F, 0x1F, 0x84, 00 ,00 ,00 ,00 ,00],
    [0x66, 0x0F, 0x1F, 0x84, 00 ,00 ,00 ,00, 00]
]

NOPTABLE = [bytearray(i) for i in NOPTABLE_impl]


def put_byteseq_at(ea, seq):
    for i in range(0, len(seq)):
        patch_byte(ea+i, seq[i])

def nop_at(ea, length):
    length -= 1
    while length >= len(NOPTABLE):
        put_byteseq_at(ea, NOPTABLE[len(NOPTABLE) - 1])
        ea += len(NOPTABLE) - 1
        length -= len(NOPTABLE) - 1

    put_byteseq_at(ea, NOPTABLE[length])


def get_call_name(insn):
    if is_call_insn(insn):
        opnd = insn.ops[0].addr
        return str(get_name(opnd))
    return ""


def is_call_to(insn, name):
    cln = get_call_name(insn)
    return cln == name or cln == ("__imp_" + name)


def toIDAHex(ea):
    return hex(ea).replace('0x', '').replace('L', '')

def has_use(itype, n):
    return has_insn_feature(itype, CF_USE1 << n)

def has_def(itype, n):
    return has_insn_feature(itype, CF_CHG1 << n)




class optimization_t(object):
    def __init__(self, name):
        self.name = name
        self.napplies = 0

    def apply(self, insn):
        return False

    def try_apply(self, insn):
        if self.apply(insn):
            print("Applied rule " + self.name + " at addr " + toIDAHex(insn.ea))
            self.napplies += 1
            return True
        return False

    def log_applies(self):
        if self.napplies != 0:
            print("Applied " + self.name + " " + str(self.napplies) + " times.")

REGSET_NBITS = 512

def make_bitset(nbits):
    res = bytearray([0 for i in range(0, nbits / 8)])
    return res

def set_bit_in_bitset(bset, n):
    bset[n >> 3] |= (1 << (n&7))

def reset_bit_in_bitset(bset, n):
    bset[n >> 3] &= ~(1 << (n & 7))

def toggle_bit_in_bitset(bset, n):
    bset[n >> 3] ^= ~(1 << (n & 7))

def bitset_has(bset, n):
    return (bset[n >> 3] & (1 << (n & 7))) != 0


def make_regset(namearr):
    result = make_bitset(REGSET_NBITS)
    for name in namearr:
        set_bit_in_bitset(result, str2reg(name))
    return result


REG_RAX = make_regset(["rax", "eax", "ax", "ah", "al"])


def terminates_bb(insn):
    return is_basic_block_end(insn, True)

def insn_uses_reg(insn, regset):
    itype = insn.itype
    for i in range(0, 8):

        op = insn.ops[i]
        if op.type == o_void:
            return False
        if not has_use(itype, i):
            continue

        if op.type == o_reg and bitset_has(regset, op.reg):
            return True
    return False


def insn_redefs_reg(insn, regset):
    itype = insn.itype
    for i in range(0, 8):

        op = insn.ops[i]
        if op.type == o_void:
            return False
        if not has_def(itype, i):
            continue

        if op.type == o_reg and bitset_has(regset, op.reg):
            return True
    return False

def find_next_uses_bb(eastart, regset):

    while True:
        insn = insn_t()
        decode_insn(insn, eastart)
        if terminates_bb(insn):
            break

        hasuse = insn_uses_reg(insn, regset)
        hasdef = insn_redefs_reg(insn, regset)
        eastart += insn.size
        if hasuse:
            yield insn
        if hasdef:
            break

def get_bb_end_insn(eastart):
    i = insn_t()

    while True:
        decode_insn(i, eastart)
        if terminates_bb(i):
            return i
        eastart += i.size
        if not is_code_at(eastart):
            break

    return None

ALLOCATOR_NAMES = {"HeapAlloc", "LocalAlloc", "malloc", "GlobalAlloc", "realloc", "_realloc", "calloc", "RtlAllocateHeap"}

def make_branch_unconditional(insn):
    target = insn.ea
    if get_byte(target) == 0x0f:
        target += 1
    patch_byte(insn.ea, 0xE9 if insn.size != 2 else 0xEB)
#100018380
def elim_impossible_zf_jump(insn):
    it = insn.itype
    if it == 85:
        #jz
        nop_at(insn.ea, insn.size)
    elif it == 79:
        make_branch_unconditional(insn)
    else:
        raise Exception("Not a valid target for elim impossible zf jump!")

def get_disline_nospace(ea):
    return GetDisasm(ea).replace(" ", "")


class nop_if_fn_rule_t(optimization_t):

    def __init__(self, name, fnname):
        self.fnname = fnname
        optimization_t.__init__(self, name)

    def apply(self, insn):
        if is_call_to(insn, self.fnname):
            nop_at(insn.ea, insn.size)
            return True
        return False


class sec_check_elim_t(nop_if_fn_rule_t):
    def __init__(self):
        nop_if_fn_rule_t.__init__(self, "Security check elimination", "__security_check_cookie")


class alloca_probe_elim_t(nop_if_fn_rule_t):
    def __init__(self):
        nop_if_fn_rule_t.__init__(self, "Alloca probe elimination", "__alloca_probe")

def opnd_are_same_regs(o1, o2):
    return o1.type == o_reg and o2.type == o_reg and o1.reg == o2.reg

def opnd_is_specific_imm(o, value):
    return o.type == o_imm and o.value == value


def is_zero_test(insn):
    it = insn.itype
    if it == NN_test and opnd_are_same_regs(insn.ops[0], insn.ops[1]):
        return True
    elif it == NN_cmp and opnd_is_specific_imm(insn.ops[1], 0):
        return True
    elif get_disline_nospace(insn.ea) == "testrax,rax":
        return True
    else:
        return False


class nullsub_elim_t(optimization_t):
    def __init__(self):
        optimization_t.__init__(self, "Nullsub elimination")

    def apply(self, insn):
        if get_call_name(insn).startswith("nullsub_"):
            nop_at(insn.ea, insn.size)
            return True
        return False


class check_alloc_ret_null_elim_t(optimization_t):
    def __init__(self):
        optimization_t.__init__(self, "Check for nullptr return in allocator elimination")

    def apply(self, insn):

        nam = get_call_name(insn)

        if nam not in ALLOCATOR_NAMES:
            return False
        huntbegin = insn.ea+insn.size

        endbb = get_bb_end_insn(huntbegin)
        if endbb is None:
            return False
        itype = endbb.itype
        if itype != NN_jnz and itype != NN_jz:
            return False

        for use in find_next_uses_bb(huntbegin, REG_RAX):
            if is_zero_test(use) and use.size+use.ea == endbb.ea:
                nop_at(use.ea, use.size)
                elim_impossible_zf_jump(endbb)
                return True

        return False

class inline_trivial_t(optimization_t):
    def __init__(self):
        optimization_t.__init__(self, "Inline trivial functions")

    def apply(self, insn):
        if not is_call_insn(insn):
            return False
        fn = get_func(insn.ops[0].addr)
        if fn is None:
            return False
        if not func_does_return(fn.start_ea):
            return False

        first_insn = None
        for i in forall_insns_in_func(fn):
            if not first_insn:
                first_insn = i
            else:
                if i.itype != NN_retn:
                    return False

        if terminates_bb(first_insn):
            return False

        if first_insn.size > insn.size:
            return False
        diff = insn.size - first_insn.size

        for i in range(0, first_insn.size):
            patch_byte(insn.ea + i, get_byte(first_insn.ea + i))

        if diff > 0:
            nop_at(insn.ea + first_insn.size, diff)

        return True



OPTIMIZATIONS = [
    sec_check_elim_t(),
    alloca_probe_elim_t(),
    nullsub_elim_t(),
check_alloc_ret_null_elim_t(),
inline_trivial_t()
]

for fn in forall_funcs():
    for insn in forall_insns_in_func(fn):
        for optimization in OPTIMIZATIONS:
            optimization.try_apply(insn)


for opt in OPTIMIZATIONS:
    opt.log_applies()




