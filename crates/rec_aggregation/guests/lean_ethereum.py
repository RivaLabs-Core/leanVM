# The recursive aggregation guest: zkDSL, not runnable Python (see
# crates/lean_compiler/zkDSL.md). One node of an aggregation tree verifies raw XMSS
# and SPHINCS+ signatures and sub-proofs OF THIS SAME BYTECODE, and publishes the
# statement digest binding its signature claims and a possibly empty list of LeanDA roots.
# It may check a blob matrix directly and retain any roots proved by its children.
# Reading order: `main` is the
# node, `verify_sub` the in-circuit copy of `lean_vm::cpu::verify`, and
# `open_stacked` the WHIR opening it dispatches into.
#
# Every `*_PLACEHOLDER` below is filled by the host at compile time
# (rec_aggregation::aggregation::placeholder_map), so one source serves every inner
# shape. Names follow doc/leanvm/preamble/macros.tex.
from snark_lib import *

# ---------------------------------------------------------------- proof stream
# The proof stream rides ONE padded witness hint of 64-bit words, three to a
# transcript scalar (the guest walks only the prefix the shape dictates); binding
# always comes from the per-scalar absorbs.
STREAM_CAP = STREAM_CAP_PLACEHOLDER
MIN_LOG_MEM = MIN_LOG_MEM_PLACEHOLDER
INV_GEN = INV_GEN_PLACEHOLDER

# ------------------------------------------------------------- the field, GF(2^192)
# A memory cell is one 64-bit word. An element of F192 = F64[Y]/(Y^3+Y+1) is a run
# of three cells, its limbs low first, computed with add192/mul192/div192; heap
# buffers of them have stride three. A product of a word and an element is
# limb-wise, three 64-bit multiplies and no reduction (`scale`).
FIELD_BITS = 192
BASE_FIELD_BITS = 64
ONE = f192(1, 0, 0)
ZERO = f192(0, 0, 0)
# Six challenges compose the F2-linear map that batches the 192 transposed
# ring-switch coordinates.
RING_MAP_SHIFTS = [32, 16, 8, 4, 2, 1]
# Exponent bit-widths: an announced 32-bit count decomposes into COUNT_BITS bits,
# its top bit constrained to zero so the native strict 32-bit bound holds; any
# structural size (sums of 2^kappa, packing offsets) fits SIZE_BITS bits; and a
# structural LOG (log_mem, tau_t, log_inv_rate), announced as an integer word and
# raised to a g-power by g_power_of_word, is below SIZE_BITS, so LOG_WORD_BITS bits
# are enough and the reconstruction IS the bound (a larger announced log cannot
# reproduce itself from this many bits).
COUNT_BITS = 33
SIZE_BITS = 34
LOG_WORD_BITS = 6

# ------------------------------------------------------------------- Fiat-Shamir
# The state is four words. Every absorbed block carries a scalar's three limbs
# and its domain tag in word 3, so a role is never smuggled through the data
# words. The seeding block has none, being fixed at the head of the chain.
DS_OBSERVE = 1
DS_SQ = 2
DS_POW_BASE = 3
DS_POW_NONCE = 4

# ----------------------------------------------------------- loop-carried chains
# A loop whose state is several values keeps ONE heap run per iteration, so a
# step is one pointer multiply rather than one per value. Each run leads with the
# four-word Fiat-Shamir state.
FS_SLOTS = 4
# A Fiat-Shamir chain carrying one accumulator (the claim batching loops).
ACC_VALUE = 4
ACC_SLOTS = 7
# One sumcheck round of the bus GKR, the table batch, or flock's multilinear rounds.
ROUND_CURSOR = 4
ROUND_CLAIM = 5
ROUND_SLOTS = 8
# One product layer of the bus GKR.
LAYER_CURSOR = 4
LAYER_PUSH = 5
LAYER_PULL = 8
LAYER_COUNT = 11
LAYER_LAMBDA = 14
LAYER_ROW = 17
LAYER_POS = 18
LAYER_SLOTS = 19
# One OOD sample of a WHIR level.
OOD_BETA = 0
OOD_Y = 3
OOD_C0 = 6
OOD_C2 = 9
OOD_SLOTS = 12

# ---------------------------------------------------- the bus: sides and blocks
# GKR sides. The layer counts mu_s are hinted and certified from the block kappas;
# GKR_ROUNDS_CAP caps the per-tree round positions (triangle rounds plus one slot
# per layer) and GKR_POINTS_CAP the point triangle (rows x MU_CAP).
PUSH_SIDE = 0
PULL_SIDE = 1
COUNT_SIDE = 2
N_GKR_SIDES = 3
GKR_ROUNDS_CAP = GKR_ROUNDS_CAP_PLACEHOLDER
MU_CAP = MU_CAP_PLACEHOLDER
GKR_POINTS_CAP = GKR_POINTS_CAP_PLACEHOLDER
# Bus blocks, flattened across the 3 sides (side s covers blocks
# [SIDE_BLOCK_START[s], SIDE_BLOCK_START[s+1])). The block STRUCTURE is
# protocol-fixed and baked: each block's coord range [BLOCK_COORD_OFF,
# +BLOCK_COORD_COUNT), per coord its COORD_TYPE kind (mirroring leaf.rs::Coord),
# COORD_CONST (the const value, a product's or gcol's g^k, else 0), and the kappa
# SOURCE map (BLOCK_KAPPA_SRC/ADJ: 0 = const adj, 1 = log_mem, 2+t = tau_t). The
# block SHAPES are all reconstructed at runtime from the certified logs: kappa
# directly, the selector bits by pinned advice-decompositions. BLOCK_TABLE names
# the table a block's flush belongs to, or NO_TABLE for the framework blocks
# (boundary, memory seed/finalize, bytecode seed/finalize); it is also what marks a
# block as owned, an owned block's fingerprint being settled by the table sumcheck
# off its table's column evaluations.
COORD_KIND_CONST = 0
COORD_KIND_COL = 1
COORD_KIND_GCOL = 2
COORD_KIND_INDEX = 3
COORD_KIND_PUBLIC = 4
COORD_KIND_PROD = 5
NO_TABLE = NO_TABLE_PLACEHOLDER
SIDE_BLOCK_START = SIDE_BLOCK_START_PLACEHOLDER
N_BLOCKS = N_BLOCKS_PLACEHOLDER
BLOCK_KAPPA_SRC = BLOCK_KAPPA_SRC_PLACEHOLDER
BLOCK_KAPPA_ADJ = BLOCK_KAPPA_ADJ_PLACEHOLDER
BLOCK_TABLE = BLOCK_TABLE_PLACEHOLDER
BLOCK_SIDE = BLOCK_SIDE_PLACEHOLDER
BLOCK_COORD_OFF = BLOCK_COORD_OFF_PLACEHOLDER
BLOCK_COORD_COUNT = BLOCK_COORD_COUNT_PLACEHOLDER
COORD_TYPE = COORD_TYPE_PLACEHOLDER
COORD_CONST = COORD_CONST_PLACEHOLDER
# Claim dedup: push/pull share their GKR point, so a column read by two blocks with
# the same kappa (across OR within the sides) is streamed and opened ONCE.
# COORD_FRESH = 1 on the first occurrence (read the stream, fill pool slot
# COORD_CLAIM_SLOT), 0 on a duplicate (reuse that slot). The count side has its own
# point, so its claims never dedup against the pair's.
COORD_FRESH = COORD_FRESH_PLACEHOLDER
COORD_CLAIM_SLOT = COORD_CLAIM_SLOT_PLACEHOLDER
# A TABLE block's coordinates, flattened into TERMS: coord c is
# Σ_{j < COORD_TERM_COUNT[c]} term(COORD_TERM_OFF[c] + j), each term a TERM_TYPE
# kind over that table's LOCAL column indices TERM_COL_A/TERM_COL_B, scaled by
# TERM_CONST. Those coords raise no claim (the table sumcheck settles them), which
# is what lets one carry a value the row DERIVES from its columns: an XOR/MUL
# result, a DEREF store, a JUMP successor. A framework coord has no terms.
COORD_TERM_OFF = COORD_TERM_OFF_PLACEHOLDER
COORD_TERM_COUNT = COORD_TERM_COUNT_PLACEHOLDER
TERM_TYPE = TERM_TYPE_PLACEHOLDER
TERM_CONST = TERM_CONST_PLACEHOLDER
TERM_COL_A = TERM_COL_A_PLACEHOLDER
TERM_COL_B = TERM_COL_B_PLACEHOLDER
N_BUS_CLAIMS = N_BUS_CLAIMS_PLACEHOLDER
INDEX_MLE_FACTORS = INDEX_MLE_FACTORS_PLACEHOLDER  # 1 + g^(2^i)
# Committed-coordinate claims (Col/GCol coords across all sides) and the deferred
# bytecode values (Public coords).
N_CLAIMS = N_CLAIMS_PLACEHOLDER
# A bus tuple's coordinates index the 2^N_TUPLE_BITS fingerprint slots (doc
# sec:gp). The stacked bytecode has BYTECODE_COLS encoding columns, stacked along
# LOG2_BYTECODE_COLS selector bits into ONE multilinear; push and pull share their
# GKR point, so the columns are opened ONCE.
N_TUPLE_BITS = 4
N_TUPLE_SLOTS = 16
BYTECODE_COLS = BYTECODE_COLS_PLACEHOLDER
LOG2_BYTECODE_COLS = LOG2_BYTECODE_COLS_PLACEHOLDER

# ------------------------------------------------------------- the eight tables
# The table sumcheck's batch carries EVERY committed column of a table, because its
# bus forms read the flushed ones and its constraint the rest; TABLE_COLS_CAP caps
# the evaluation frame. ETA_OFFSET[t] starts table t's disjoint range of zc_xi
# powers; the three bus forms take ETA_FORM_BASE + side, the SAME three powers for
# every table, and that sharing is what makes the batch's target derivable from the
# three leaf claims. FLOORS[t] is the table's tau floor (BLAKE2s is sized to
# flock's instance count, >= 2^3).
TABLE_XOR64 = 0
TABLE_MUL64 = 1
TABLE_SET = 2
TABLE_DEREF = 3
TABLE_JUMP = 4
TABLE_BLAKE2s = 5
TABLE_XOR192 = 6
TABLE_MUL192 = 7
N_TABLES = N_TABLES_PLACEHOLDER
FLOORS = [0, 0, 0, 0, 0, 3, 0, 0]
N_TABLE_COLS = N_TABLE_COLS_PLACEHOLDER
TABLE_COLS_CAP = TABLE_COLS_CAP_PLACEHOLDER
ETA_OFFSET = ETA_OFFSET_PLACEHOLDER
ETA_FORM_BASE = ETA_FORM_BASE_PLACEHOLDER
N_ETA_POWS = N_ETA_POWS_PLACEHOLDER

# ------------------------------------------------------------ flock (the R1CS)
# Univariate skip: K_SKIP variables fold in one skip round (half-domain 2^K_SKIP
# phi8 nodes), then N_FIXED_CHALLENGE_ROUNDS fixed inner rounds (FIXED_CHALLENGES),
# then sampled outer rounds. LAGRANGE_INV_* are the one baked inverse barycentric
# denominator per domain (combined, S). The zerocheck point/round buffers are sized
# at runtime in the exponent (m = K_LOG + tau_5 and m - 6, both certified);
# LINCHECK_ROUNDS = K_LOG - K_SKIP is protocol-fixed and PIN_COLUMN is the
# const-pin column. FIXED_CHALLENGES and PHI8_NODES hold three words an element.
K_SKIP = K_SKIP_PLACEHOLDER
N_FIXED_CHALLENGE_ROUNDS = N_FIXED_CHALLENGE_ROUNDS_PLACEHOLDER
FIXED_CHALLENGES = FIXED_CHALLENGES_PLACEHOLDER
PHI8_NODES = PHI8_NODES_PLACEHOLDER
LAGRANGE_INV_COMBINED = LAGRANGE_INV_COMBINED_PLACEHOLDER
LAGRANGE_INV_S = LAGRANGE_INV_S_PLACEHOLDER
LINCHECK_ROUNDS = LINCHECK_ROUNDS_PLACEHOLDER
PIN_COLUMN = PIN_COLUMN_PLACEHOLDER
K_LOG = K_LOG_PLACEHOLDER
SLOT_STRIDE_LOG = SLOT_STRIDE_LOG_PLACEHOLDER  # = K_LOG - LOG_PACKING (=8); the q_flock slot stride

# ------------------------------------------------- the stacked WHIR opening
# The opening is dispatched by the certified committed log-size m through `match`.
# The LIG_* tables carry one row per (rate, m), emitted from the same
# derive_profile/level_shapes the prover uses: scalars index as TBL[m_idx],
# per-level values as TBL[m_idx * LIG_MAX_LEVELS + lvl] where m_idx is the
# flattened rate-major configuration index, and the subspace vanishing constants
# with the LIG_MAX_VANISH_LEN stride.
LIG_MIN_LOG_SIZE = LIG_MIN_LOG_SIZE_PLACEHOLDER
LIG_N_LOG_SIZES = LIG_N_LOG_SIZES_PLACEHOLDER
LIG_N_RATES = LIG_N_RATES_PLACEHOLDER
# Committed-column kappa sources (0 = const COL_KAPPA_ADJ, 1 = log_mem, 2+t = tau_t)
# and the PCS floor for the stacked size.
N_COMMITTED_COLS = N_COMMITTED_COLS_PLACEHOLDER
N_COLUMN_LOGS = N_COLUMN_LOGS_PLACEHOLDER
COL_KAPPA_SRC = COL_KAPPA_SRC_PLACEHOLDER
COL_KAPPA_ADJ = COL_KAPPA_ADJ_PLACEHOLDER
PCS_MIN_MU = PCS_MIN_MU_PLACEHOLDER
# Global maxima; StackBuf frame sizes are parse-time, so they must be baked.
LIG_MAX_LEVELS = LIG_MAX_LEVELS_PLACEHOLDER
LIG_MAX_VANISH_LEN = LIG_MAX_VANISH_LEN_PLACEHOLDER
LIG_MAX_OOD_SAMPLES = LIG_MAX_OOD_SAMPLES_PLACEHOLDER
LIG_LOG_MSG_COLS_CAP = LIG_LOG_MSG_COLS_CAP_PLACEHOLDER
YR_LOG_CAP = YR_LOG_CAP_PLACEHOLDER
MAX_STACK_LOG = LIG_MIN_LOG_SIZE + LIG_N_LOG_SIZES - 1
LIG_N_LEVELS = LIG_N_LEVELS_PLACEHOLDER
LIG_YR_LEVEL = LIG_YR_LEVEL_PLACEHOLDER
LIG_YR_LOG_LEN = LIG_YR_LOG_LEN_PLACEHOLDER
LIG_YR_LEN = LIG_YR_LEN_PLACEHOLDER
LIG_TOTAL_FOLDS = LIG_TOTAL_FOLDS_PLACEHOLDER
LIG_MAX_QUERIES = LIG_MAX_QUERIES_PLACEHOLDER
LIG_MAX_SQUEEZES = LIG_MAX_SQUEEZES_PLACEHOLDER
LIG_MAX_INTERLEAVE = LIG_MAX_INTERLEAVE_PLACEHOLDER
LIG_POSITIONS_LEN = LIG_POSITIONS_LEN_PLACEHOLDER
LIG_CAP_DEPTH = LIG_CAP_DEPTH_PLACEHOLDER
LIG_CAP_OFF = LIG_CAP_OFF_PLACEHOLDER
LIG_CAP_LEN = LIG_CAP_LEN_PLACEHOLDER
LIG_QUERY_GRIND_BITS = LIG_QUERY_GRIND_BITS_PLACEHOLDER
LIG_OOD_SAMPLES = LIG_OOD_SAMPLES_PLACEHOLDER
LIG_QUERIES = LIG_QUERIES_PLACEHOLDER
LIG_FOLDS = LIG_FOLDS_PLACEHOLDER
LIG_INTERLEAVE = LIG_INTERLEAVE_PLACEHOLDER
LIG_LEAF_BLOCKS = LIG_LEAF_BLOCKS_PLACEHOLDER
LIG_ROW_CAP = LIG_ROW_CAP_PLACEHOLDER
LIG_PATH_CAP = LIG_PATH_CAP_PLACEHOLDER
LIG_TREE_DEPTH = LIG_TREE_DEPTH_PLACEHOLDER
LIG_SQUEEZES = LIG_SQUEEZES_PLACEHOLDER
LIG_POSITIONS_OFF = LIG_POSITIONS_OFF_PLACEHOLDER
LIG_LOG_MSG_COLS = LIG_LOG_MSG_COLS_PLACEHOLDER
LIG_RESIDUAL_FOLD_OFF = LIG_RESIDUAL_FOLD_OFF_PLACEHOLDER
LIG_RESIDUAL_PREFIX_LEN = LIG_RESIDUAL_PREFIX_LEN_PLACEHOLDER
LIG_FOLDS_OFF = LIG_FOLDS_OFF_PLACEHOLDER
LIG_VANISH_OFF = LIG_VANISH_OFF_PLACEHOLDER
LIG_VANISH_VALS = LIG_VANISH_VALS_PLACEHOLDER  # words: the novel basis lives in F64
LIG_VANISH_INVS = LIG_VANISH_INVS_PLACEHOLDER
LIG_N_CANDIDATES = LIG_N_CANDIDATES_PLACEHOLDER
LIG_MIN_SHIFT_INV = LIG_MIN_SHIFT_INV_PLACEHOLDER
# eval_b claim descriptors. CLAIM_POINT_BUF says which point buffer a pooled
# claim's x-part lives in, CLAIM_COMMITTED_COL maps it to the compact index of the
# committed column it must open (a virtual BLAKE2s value claim maps to QFLOCK),
# CLAIM_QFLOCK_SLOT_BITS holds the fixed packed-slot bits of every logical claim
# (zero for a non-virtual one), and QFLOCK_COMMITTED_COL is the ring-switch target.
POINT_BUF_ZETA = 0
POINT_BUF_RHO = 1
POINT_BUF_PI = 2
POINT_BUF_QFLOCK_RHO = 3
CLAIM_POINT_BUF = CLAIM_POINT_BUF_PLACEHOLDER
CLAIM_COMMITTED_COL = CLAIM_COMMITTED_COL_PLACEHOLDER
CLAIM_QFLOCK_SLOT_BITS = CLAIM_QFLOCK_SLOT_BITS_PLACEHOLDER
QFLOCK_COMMITTED_COL = QFLOCK_COMMITTED_COL_PLACEHOLDER
QFLOCK_VARS_CAP = QFLOCK_VARS_CAP_PLACEHOLDER

# ------------------------------------------------------ statements and deferral
# A node defers three claims on fixed polynomials. DEFER_SIZE is the region one
# sub-proof's verification exports, in field elements (a bytecode point plus the
# flock lincheck data, see verify_sub's defer_out layout); DEFER_STMT_* index the
# batched claims a node's OWN statement carries. The Fiat-Shamir seed rides the
# statement rather than being baked, so one compiled guest verifies proofs of any
# inner program.
BYTECODE_LOG = BYTECODE_LOG_PLACEHOLDER  # log rows of the bytecode blocks
DEFER_SIZE = DEFER_SIZE_PLACEHOLDER
BYTECODE_VARS = BYTECODE_VARS_PLACEHOLDER  # = BYTECODE_LOG + LOG2_BYTECODE_COLS
# The exported record's layout: the shared bytecode point, then the flock data.
FRESH_BC_VALUE = BYTECODE_VARS
FRESH_ALPHA = BYTECODE_VARS + 1
FRESH_Z_SKIP = BYTECODE_VARS + 2
FRESH_ZCHI = BYTECODE_VARS + 3
FRESH_LINCHECK_RS = FRESH_ZCHI + LINCHECK_ROUNDS
FRESH_Z_PARTIAL = FRESH_LINCHECK_RS + LINCHECK_ROUNDS
FRESH_MATPART = FRESH_Z_PARTIAL + 2 ** K_SKIP
DEFER_STMT_CELLS = BYTECODE_VARS + 1 + 2 * K_LOG + 2
DEFER_STMT_BC_VALUE = BYTECODE_VARS
DEFER_STMT_MAT_POINT = BYTECODE_VARS + 1
DEFER_STMT_A_VALUE = BYTECODE_VARS + 1 + 2 * K_LOG
DEFER_STMT_B_VALUE = BYTECODE_VARS + 2 + 2 * K_LOG
AGG_SEED_0 = AGG_SEED_0_PLACEHOLDER
AGG_SEED_1 = AGG_SEED_1_PLACEHOLDER
AGG_SEED_2 = AGG_SEED_2_PLACEHOLDER
AGG_SEED_3 = AGG_SEED_3_PLACEHOLDER
# The statement digest's preimage: the STMT_HEADER header words (the seed, the
# signer-set digest, which itself binds the epoch groups and every count, and the
# DA root-list digest), then the deferred elements' three limbs each, zero-filled
# to whole blocks. No domain tag: the seed leads, and it binds this bytecode and
# flock's R1CS.
STMT_HEADER = STMT_HEADER_PLACEHOLDER
STMT_PAD = STMT_PAD_PLACEHOLDER
STMT_BLOCKS = STMT_BLOCKS_PLACEHOLDER
# The declared lists are hashed with plain BLAKE2s over a flat run of words, 64
# bytes a compression. A block's byte counter is a runtime value and the ISA has no
# integer addition, so it splits as in doc §sec:prog-byte-counter: a window of
# SIGNERS_WINDOW blocks shares one base 64·SIGNERS_WINDOW·q, whose set bits all sit
# above the window's own offsets 64(j+1), so a block's counter word is one XOR. The
# base comes from the window loop's own counter, and the one block whose offset
# overlaps it takes the next window's base instead.
SIGNERS_WINDOW = SIGNERS_WINDOW_PLACEHOLDER
SIGNERS_WINDOW_LOG = SIGNERS_WINDOW_LOG_PLACEHOLDER
SIGNERS_MAX_WINDOWS = SIGNERS_MAX_WINDOWS_PLACEHOLDER
SIGNERS_COUNT_BITS = SIGNERS_COUNT_BITS_PLACEHOLDER
# The lists a hash tail walks (`tail_blocks`).
LIST_PLAIN = 0
LIST_KEYS = 1
LIST_SPHINCS = 2
LIST_CHILD_KEYS = 3
LIST_CHILD_SPHINCS = 4
# BLAKE2s's parameterized initial chaining value, which every hash here starts from,
# and the flag word of a final block's metadata.
BLAKE2S_IV_0 = BLAKE2S_IV_0_PLACEHOLDER
BLAKE2S_IV_1 = BLAKE2S_IV_1_PLACEHOLDER
BLAKE2S_IV_2 = BLAKE2S_IV_2_PLACEHOLDER
BLAKE2S_IV_3 = BLAKE2S_IV_3_PLACEHOLDER
MD_FINAL = MD_FINAL_PLACEHOLDER

# ---------------------------------------------------------- XMSS (host-supplied)
# Every 16-byte native value (tweak, digest, chain tip, sibling, public parameter)
# is two words, a 32-byte one (a message, a key) four. A tweak's first word holds
# its type and sub-position, its second the index at bit 32 (`xmss::make_tweak`):
# XM_* are the first words, as the host read them out of `make_tweak`, and
# XM_INDEX_WEIGHT[b] is what bit b of an index weighs in the second, an index being
# its set bits summed. A sub-position weighs XM_P_MUL a unit.
V = V_PLACEHOLDER
W = W_PLACEHOLDER
TARGET_SUM = TARGET_SUM_PLACEHOLDER
LOG_LIFETIME = LOG_LIFETIME_PLACEHOLDER
CHAIN_LENGTH = 2 ** W
CHAIN_STEPS = CHAIN_LENGTH - 1
XM_ENC_TWEAK = XM_ENC_TWEAK_PLACEHOLDER
XM_PK_TWEAK = XM_PK_TWEAK_PLACEHOLDER
XM_CHAIN_TWEAK = XM_CHAIN_TWEAK_PLACEHOLDER
XM_MERKLE_TWEAK = XM_MERKLE_TWEAK_PLACEHOLDER
XM_INDEX_WEIGHT = XM_INDEX_WEIGHT_PLACEHOLDER
XM_P_MUL = XM_P_MUL_PLACEHOLDER
# Digits packed per digest word: W bits each in GF(2^64)'s monomial budget (the
# word's leftover top bits are ground to zero by the signer).
DIGITS_PER_WORD = V / 2
TIP_WORDS = 2 * V
WOTS_PK_BLOCKS = (2 + V) / 4  # prefix (tweak, pp) + V tips, eight words a block

# ------------------------------------------------------ SPHINCS+ (host-supplied)
# The scheme's own letters, prefixed SP_ where XMSS has the same one.
SP_V = SP_V_PLACEHOLDER
SP_W = SP_W_PLACEHOLDER
SP_TARGET_SUM = SP_TARGET_SUM_PLACEHOLDER
SP_D = SP_D_PLACEHOLDER
SP_HEIGHTS = SP_HEIGHTS_PLACEHOLDER   # h_lay, one per hypertree layer, top first
SP_SUFFIX = SP_SUFFIX_PLACEHOLDER     # SP_SUFFIX[lay] = sum of h_j for j >= lay
SP_A = SP_A_PLACEHOLDER
SP_K = SP_K_PLACEHOLDER
SP_H = SP_H_PLACEHOLDER               # the total hypertree height, SP_SUFFIX[0]
SP_CHAIN_LENGTH = 2 ** SP_W
SP_CHAIN_STEPS = SP_CHAIN_LENGTH - 1
SP_DIGITS_PER_WORD = SP_V / 2
SP_TIP_WORDS = 2 * SP_V
SP_LEAF_BLOCKS = (2 + SP_V) / 4       # prefix (tweak, pp) + V tips, eight words a block
SP_N_FTS = SP_K - 1                   # the forest drops the last index's tree
SP_ROOT_BLOCKS = (2 + SP_N_FTS) / 4
# The message digest is h + k*a bits of a BLAKE2s output, within its first three
# words, so the bit buffer holds three words' decompositions.
SP_BIT_LANES = 3
SP_BIT_CELLS = SP_BIT_LANES * BASE_FIELD_BITS
# Native tweak first words, including the protocol domain separator and type.
SP_TW_CHAIN = SP_TW_CHAIN_PLACEHOLDER
SP_TW_LEAF = SP_TW_LEAF_PLACEHOLDER
SP_TW_NODE = SP_TW_NODE_PLACEHOLDER
SP_TW_ENC = SP_TW_ENC_PLACEHOLDER
SP_TW_FTS_LEAF = SP_TW_FTS_LEAF_PLACEHOLDER
SP_TW_FTS_NODE = SP_TW_FTS_NODE_PLACEHOLDER
SP_TW_FTS_ROOTS = SP_TW_FTS_ROOTS_PLACEHOLDER
SP_TW_MSG = SP_TW_MSG_PLACEHOLDER
# Tweak layout: protocol_domain_sep | type | layer | zero | p in the first word,
# tree | index in the second, each 32-bit field within one word.
SP_LAY_MUL = 2 ** 16
SP_P_MUL = 2 ** 32
SP_TAU_POS = 0
SP_J_POS = 32
SP_CHAIN_MUL = SP_CHAIN_LENGTH * SP_P_MUL   # chain i's tweaks start at p = 2^w * i
# The encoding counter, LE_32 in the low four bytes of its word: bounded by
# decomposing exactly that many bits, so the guest accepts no preimage the native
# verifier cannot parse.
SP_COUNTER_BITS = 32

# --------------------------------------------------------------- node capacities
# MAX_KEYS caps the coverage table's slots, both schemes' declared keys and their
# duplicates, which is what the coverage range check needs below 2^MIN_LOG_MEM;
# MAX_RECURSIONS is the arity of an aggregation tree; MAX_EPOCHS caps the runtime
# number of XMSS epoch groups.
MAX_KEYS = MAX_KEYS_PLACEHOLDER
MAX_DA_ROOTS = MAX_DA_ROOTS_PLACEHOLDER
DA_ROOT_COUNTS = DA_ROOT_COUNTS_PLACEHOLDER
MAX_RECURSIONS = MAX_RECURSIONS_PLACEHOLDER
MAX_EPOCHS = MAX_EPOCHS_PLACEHOLDER


# ---------------------------------- LeanDA ------------------------------------------
# Blob and cell widths are fixed. The row count is hinted and bounded by DA_MAX_ROWS;
# the Merkle trees dispatch on the checked log of its padded value.
DA_LOG_K = DA_LOG_K_PLACEHOLDER
DA_LOG_CELL = DA_LOG_CELL_PLACEHOLDER
DA_MAX_ROWS = DA_MAX_ROWS_PLACEHOLDER
DA_LOG_MAX_ROWS = DA_LOG_MAX_ROWS_PLACEHOLDER
DA_PAD_CELL = DA_PAD_CELL_PLACEHOLDER
DA_PAD_ROW = DA_PAD_ROW_PLACEHOLDER

DA_CELL = 2 ** DA_LOG_CELL                      # symbols in a cell
DA_BLOCK_BITS = DA_LOG_K + 1 - DA_LOG_CELL      # log of the cells per row
DA_CELLS = 2 ** DA_BLOCK_BITS                   # cells per row
DA_PREFIX_CELLS = 2 ** (DA_LOG_K - DA_LOG_CELL)    # cells in the first half
DA_CELL_BLOCKS = DA_CELL // 8                   # BLAKE2s blocks in one cell
DA_ROW_BLOCKS = DA_PREFIX_CELLS // 2               # BLAKE2s blocks in one row digest
DA_TREE_ARMS = DA_LOG_MAX_ROWS + 1              # tree depths the row count can dispatch to

# =================================== field helpers ==================================


@inline
def scale(s, x):
    # A word times an element, limb by limb.
    return [s * x[0], s * x[1], s * x[2]]


@inline
def add64(x, s):
    # An element plus a word: only the low limb moves.
    return [x[0] + s, x[1], x[2]]


@inline
def fixed_challenge(i: Const):
    return f192(FIXED_CHALLENGES[3 * i], FIXED_CHALLENGES[3 * i + 1], FIXED_CHALLENGES[3 * i + 2])


@inline
def phi8(i: Const):
    return f192(PHI8_NODES[3 * i], PHI8_NODES[3 * i + 1], PHI8_NODES[3 * i + 2])


# ==================================== Fiat-Shamir ===================================


@inline
def fs_next(state, cursor):
    # Fetch, observe and advance in one act: read the scalar under `cursor`, fold
    # it into the state, and hand back the successor state, the scalar, AND the
    # cursor stepped one scalar on. Reading and absorbing are inseparable here, so
    # no proof-stream word can enter the computation unbound: the soundness
    # invariant the whole guest rests on. All three returns alias into the caller.
    block = StackBuf(4)
    block[0:3] = cursor[0:3]
    block[3] = DS_OBSERVE
    nb = StackBuf(4)
    blake2s(state, block, nb)
    return nb, block[0:3], cursor * GEN ** 3


@inline
def fs_next_half(state, cursor):
    # `fs_next` of a 128-bit half of a Merkle root, which rides the stream as a
    # scalar with a zero top limb (merkle.rs `scalars_to_hash`).
    block = StackBuf(4)
    block[0:3] = cursor[0:3]
    block[3] = DS_OBSERVE
    assert block[2] == 0
    nb = StackBuf(4)
    blake2s(state, block, nb)
    return nb, block[0:3], cursor * GEN ** 3


@inline
def obs(state, x):
    # Bind one scalar into the chain: state <- compress(state, (x, DS_OBSERVE)).
    nb = StackBuf(4)
    blake2s(state, [x, DS_OBSERVE], nb)
    return nb


@inline
def obs_at(state, ptr):
    # `obs` of the scalar at a heap pointer, read straight into the block.
    block = StackBuf(4)
    block[0:3] = ptr[0:3]
    block[3] = DS_OBSERVE
    nb = StackBuf(4)
    blake2s(state, block, nb)
    return nb


@inline
def squeeze(state):
    # Ratchet: the digest is the new state, its first three words the challenge.
    nb = StackBuf(4)
    blake2s(state, [0, 0, 0, DS_SQ], nb)
    return nb, nb[0:3]


# ============================ bits, logs, and the exponent ==========================


@inline
def bind_bits(bits_ptr, value, n: Const):
    # Tie an advice bit run back to the word it decomposes. Booleanity is a
    # write-once pin: the cell already holds the bit, so storing its square IS the
    # assert, one instruction shorter than a separate equality.
    acc = 0
    for i in unroll(0, n):
        b = bits_ptr[GEN ** i]
        bits_ptr[GEN ** i] = b * b
        acc += b * 2 ** i
    assert acc == value
    return


def exponent_tables():
    # Read-only lookup tables over the exponent domain, indexed at runtime g-powers
    # (so they must be heap, not stack): g_logs_pow2[g^j] = 2^j raises a g-power's
    # log, and g_squares[g^j] = g^(2^j) turns integer sums of powers of two into
    # field products. Both span SIZE_BITS because verify_log2_ceil bounds its result
    # there, so g_log reaches g^(SIZE_BITS-1) and indexes g_logs_pow2 at it; sizing
    # to COUNT_BITS would leave that lookup reading a prover-chosen cell.
    g_logs_pow2 = HeapBuf(SIZE_BITS)
    for j in unroll(0, SIZE_BITS):
        g_logs_pow2[GEN ** j] = 2 ** j
    g_squares = HeapBuf(SIZE_BITS)
    sq_run = GEN
    for j in unroll(0, SIZE_BITS):
        g_squares[GEN ** j] = sq_run
        sq_run *= sq_run
    return g_logs_pow2, g_squares


def g_power_of_word(value, g_squares, nbits: Const):
    # g^value for a concrete integer `value` < 2^nbits: advice-decompose its bits,
    # tie them back to the word, and assemble Π g^(bit_j·2^j).
    bits = HeapBuf(GEN ** nbits)
    hint_decompose_bits(bits, value, nbits)
    word = 0
    g_value = GEN ** 0
    for j in unroll(0, nbits):
        bit = bits[GEN ** j]
        assert bit * bit == bit
        word += bit * (2 ** j)
        g_value *= (1 + bit * (g_squares[GEN ** j] + 1))
    assert word == value
    return g_value


def verify_log2_ceil(bits_buf, g_logs_pow2, g_squares, floor: Const, nbits: Const):
    # Given `nbits` bits already in bits_buf, return (g_log, exp_prod) for
    # word = Σ bit_j 2^j: exp_prod = g^word and g_log = g^max(log2_ceil(word),
    # floor). g_log is prover advice, pinned to log2_ceil(word) by psum[g_log] ==
    # word (word < 2^log, the == 2^log case via g_logs_pow2) and word > 2^(log-1)
    # (waived at floor). Callers fill the bits and tie word or exp_prod to their
    # value. NB: log2 here is the base-2 log of the integer word, not the discrete
    # log base g that `log(...)` means.
    psum_buf = HeapBuf(SIZE_BITS + 1)  # psum_buf[g^j] = value of bits [0, j)
    psum_buf[GEN ** 0] = 0
    word = 0
    exp_prod = GEN ** 0
    for j in unroll(0, nbits):
        bit = bits_buf[GEN ** j]
        assert bit * bit == bit
        exp_prod *= (1 + bit * (g_squares[GEN ** j] + 1))
        word += bit * (2 ** j)
        psum_buf[GEN ** (j + 1)] = word
    for j in unroll(nbits + 1, SIZE_BITS + 1):
        psum_buf[GEN ** j] = word
    g_log = hint_log2_ceil(bits_buf, nbits, floor)  # prover advice; verified below
    assert log(g_log) < SIZE_BITS
    assert log(g_log / (GEN ** floor)) < SIZE_BITS
    low_bits = psum_buf[g_log]                  # value of bits [0, log)
    high_bits = low_bits + word                 # value of bits [log, nbits)
    assert high_bits * low_bits == 0            # word < 2^log (high bits clear) OR ...
    assert high_bits * (word + g_logs_pow2[g_log]) == 0  # ... word == 2^log
    if g_log != GEN ** floor:
        # minimality (word > 2^(log-1)); skip at g_log == g^0, where word is in
        # {0,1}, its ceil-log 0 already minimal and psum_buf[g^-1] out of range.
        if g_log != GEN ** 0:
            low_bits_prev = psum_buf[g_log * INV_GEN]  # bits [0, log-1)
            word_vs_2logprev = word + g_logs_pow2[g_log * INV_GEN]  # 0 iff word == 2^(log-1)
            assert (low_bits_prev + word) * word_vs_2logprev != 0
    return g_log, exp_prod


def log2_ceil_in_the_exponent(g_N, g_logs_pow2, g_squares, floor: Const, nbits: Const):
    # g^log2_ceil(N) given g_N = g^N (N < 2^nbits). There is no in-circuit log, so
    # the prover hints N's bits; they are verified and tied back, the value they
    # decode to having to equal g_N.
    bits = HeapBuf(GEN ** nbits)
    hint_decompose_bits_exponent(bits, g_N, nbits)
    g_log, g_bits_value = verify_log2_ceil(bits, g_logs_pow2, g_squares, floor, nbits)
    assert g_bits_value == g_N
    return g_log


def decode_query_bits(squeezed: StackBuf(3), positions_out, bit_ptrs_out, depth: Const):
    # The squeezed challenge's 192 bits are advice-decomposed HERE, a limb at a time,
    # boolean-constrained and tied back by reconstruction; each depth-bit group also
    # becomes a query position (little-endian), with a pointer to its bit run (the
    # Merkle direction bits). The bits live in FRAME cells, every index into them
    # being compile-time, and `addr` names the run so the direction-bit pointers
    # still reach it.
    per_word = FIELD_BITS // depth
    bits = StackBuf(FIELD_BITS)
    bits_ptr = addr(bits)
    hint_decompose_bits(bits, squeezed[0], BASE_FIELD_BITS)
    hint_decompose_bits(bits_ptr * GEN ** 64, squeezed[1], BASE_FIELD_BITS)
    hint_decompose_bits(bits_ptr * GEN ** 128, squeezed[2], BASE_FIELD_BITS)
    acc0 = 0
    acc1 = 0
    acc2 = 0
    for j in unroll(0, per_word):
        base_bit = j * depth
        lane = base_bit // 64
        shift = base_bit % 64
        # A group inside one limb is one run of bits; a group straddling a limb
        # boundary splits into the two runs that do stay inside one. `b // cut == 0`
        # IS `b < cut`, the DSL's `if` comparing for equality only.
        cut = 64 - shift  # bits of this group below the next limb
        p_lo = 0
        p_hi = 0
        for b in unroll(0, depth):
            t = bits[base_bit + b]
            bits[base_bit + b] = t * t  # booleanity, as a write-once pin
            if b // cut == 0:
                p_lo += t * 2 ** b
            else:
                p_hi += t * 2 ** (b - cut)
        if const(lane == 0):
            acc0 += p_lo * 2 ** shift
        if const(lane == 1):
            acc1 += p_lo * 2 ** shift
        if const(lane == 2):
            acc2 += p_lo * 2 ** shift
        # position = p_lo + 2^cut * p_hi: multiplying by X^cut concatenates the two
        # runs, both degrees staying below 64.
        if cut // depth == 0:  # `cut < depth`: this group straddles the boundary
            positions_out[GEN ** j] = p_lo + p_hi * 2 ** cut
            if const(lane == 0):
                acc1 += p_hi
            if const(lane == 1):
                acc2 += p_hi
        else:
            positions_out[GEN ** j] = p_lo
        bit_ptrs_out[GEN ** j] = bits_ptr * GEN ** base_bit
    for i in unroll(per_word * depth, FIELD_BITS):
        t = bits[i]
        bits[i] = t * t
        if const(i // 64 == 0):
            acc0 += t * 2 ** (i % 64)
        if const(i // 64 == 1):
            acc1 += t * 2 ** (i % 64)
        if const(i // 64 == 2):
            acc2 += t * 2 ** (i % 64)
    assert acc0 == squeezed[0]
    assert acc1 == squeezed[1]
    assert acc2 == squeezed[2]
    return


def grind_check(state: StackBuf(4), nonce: StackBuf(3), nbits_g):
    # WHIR fold/query grinding: digest = H(H(state, POW_BASE), (nonce, POW_NONCE)),
    # whose low nbits (nbits_g = g^nbits) must be zero. The PoW window of
    # transcript::pow_bits_ok is `digest.0 & ((1 << bits) - 1)` with nbits < 64, so
    # it lives entirely in the digest's first word: only that word is
    # advice-decomposed and verified. The caller absorbs the full field nonce
    # afterwards. The honest prover searches the deterministic u64 subset while
    # verification permits the full field: each candidate still costs one hash and
    # succeeds with probability 2^-bits.
    if nbits_g == GEN ** 0:
        assert_eq192(nonce, ZERO)  # native canonical zero-work nonce
    base = StackBuf(4)
    blake2s(state, [0, 0, 0, DS_POW_BASE], base)
    out = StackBuf(4)
    blake2s(base, [nonce, DS_POW_NONCE], out)
    # Frame cells for the unrolled pass (no DEREF per bit), named by `addr` for the
    # zero-check walk, whose bound is runtime and so must index a pointer.
    word_bits = StackBuf(BASE_FIELD_BITS)
    hint_decompose_bits(word_bits, out[0], BASE_FIELD_BITS)
    word_ptr = addr(word_bits)
    bind_bits(word_ptr, out[0], BASE_FIELD_BITS)
    for xb in mul_range(1, nbits_g):
        assert word_ptr[xb] == 0
    return


# =============================== multilinear primitives =============================


@inline
def eq_weight(ch, count: Const, idx: Const, msb_span: Const):
    # The eq-tensor weight of compile-time index `idx` against the challenge run
    # ch[0..count), three words an element: prod_c eq(bit(idx), ch[c]), where the
    # bit is bit c of idx (msb_span == 0) or bit (msb_span - 1 - c) (an MSB-first
    # walk over an msb_span-bit index).
    w = ONE
    for c in unroll(0, count):
        k = 3 * c
        cv = ch[k:k + 3]
        if msb_span == 0:
            bit = (idx // (2 ** c)) % 2
        else:
            bit = (idx // (2 ** (msb_span - 1 - c))) % 2
        if bit == 1:
            w = mul192(w, cv)
        else:
            w = mul192(w, add192(ONE, cv))
    return w


@inline
def eqtree(point_ptr, out, n_coords: Const):
    # The eq tensor of the n_coords challenges at point_ptr[0..n_coords), built by
    # doubling into out (size 2^(n_coords+1) - 2 elements); the final 2^n_coords
    # values start at element 2^n_coords - 2.
    r0 = point_ptr[0:3]
    out[0:3] = add192(ONE, r0)
    out[3:6] = r0
    for t in unroll(1, n_coords):
        k = 3 * t
        rt = point_ptr[k:k + 3]
        one_plus_rt = add192(ONE, rt)
        for i in unroll(0, 2 ** t):
            src = 3 * (2 ** t - 2 + i)
            lo = 3 * (2 ** (t + 1) - 2 + i)
            hi = 3 * (2 ** (t + 1) - 2 + 2 ** t + i)
            pw = out[src:src + 3]
            out[lo:lo + 3] = mul192(pw, one_plus_rt)
            out[hi:hi + 3] = mul192(pw, rt)
    return


@inline
def lag64(z, out, node_base: Const):
    # The 64 phi8-domain Lagrange NUMERATORS at z over nodes
    # PHI8_NODES[node_base .. node_base + 64]: out[i] = prod_{j != i} (z +
    # PHI8_NODES[node_base + j]), three cells an element. Every barycentric
    # denominator over an aligned phi8 window is the same element, so callers scale
    # the finished sum once by LAGRANGE_INV_S / LAGRANGE_INV_COMBINED instead of the
    # numerators one by one.
    pre = StackBuf(3 * 65)
    pre[0:3] = ONE
    for i in unroll(0, 64):
        k = 3 * i
        pre[k + 3:k + 6] = mul192(pre[k:k + 3], add192(z, phi8(node_base + i)))
    suf = StackBuf(3 * 65)
    suf[192:195] = ONE
    for i in unroll(0, 64):
        k = 3 * (63 - i)
        suf[k:k + 3] = mul192(suf[k + 3:k + 6], add192(z, phi8(node_base + 63 - i)))
    for i in unroll(0, 64):
        k = 3 * i
        out[k:k + 3] = mul192(pre[k:k + 3], suf[k + 3:k + 6])
    return


def eq_prefix_chain(chain, seed: StackBuf(3), a, b, count_g):
    # Prefix products of eq(a_k, b_k) = 1 + a_k + b_k from `seed`, so a reader picks
    # the partial product up at its own certified length. Entry t is written from
    # inputs with index < t only, so a garbage tail past a buffer's written extent
    # cannot corrupt any shorter prefix. Every buffer holds three words an element.
    chain[0:3] = seed
    for xk in mul_range(1, count_g):
        x3 = xk ** 3
        nxt = x3 * GEN ** 3
        chain[nxt:nxt + 3] = mul192(chain[x3:x3 + 3], add192(ONE, add192(a[x3:x3 + 3], b[x3:x3 + 3])))
    return


def rs_eq_run(chain, z_vals, point, count_g):
    # One run of the telescoped ring-switch product E = sum_k c_k * prod_j
    # (z_j^(2^k) + 1 + ris_j): coordinate x multiplies row k by (z^(2^k) + 1 +
    # point_x), z evolving by squaring per row. The runtime coordinates walk
    # OUTSIDE and the fixed Frobenius powers inside, so nothing stores a z-power
    # table. A row is BASE_FIELD_BITS elements.
    for xk in mul_range(1, count_g):
        x3 = xk ** 3
        zv = z_vals[x3:x3 + 3]
        one_plus = add192(ONE, point[x3:x3 + 3])
        row = chain * xk ** (3 * BASE_FIELD_BITS)
        nxt = row * GEN ** (3 * BASE_FIELD_BITS)
        for k in unroll(0, BASE_FIELD_BITS):
            c = 3 * k
            nxt[c:c + 3] = mul192(row[c:c + 3], add192(zv, one_plus))
            if k != BASE_FIELD_BITS - 1:
                zv = mul192(zv, zv)
    return


def fold_final_msg(msg, point, log_len: Const):
    # Weighted fold of the final_msg multilinear over 2^log_len values (log_len is
    # the candidate's yr_log_n; the frame buffers use the global max size).
    l0 = StackBuf(3 * 2 ** YR_LOG_CAP)
    p0 = point[0:3]
    for t in unroll(0, 2 ** log_len // 2):
        k = 3 * t
        lo = 6 * t
        hi = 6 * t + 3
        a = msg[lo:lo + 3]
        l0[k:k + 3] = add192(a, mul192(p0, add192(a, msg[hi:hi + 3])))
    cursor = l0
    n = 2 ** log_len // 2
    for j in unroll(1, log_len):
        pj_off = 3 * j
        pj = point[pj_off:pj_off + 3]
        nxt = StackBuf(3 * 2 ** YR_LOG_CAP)
        for t in unroll(0, n // 2):
            k = 3 * t
            lo = 6 * t
            hi = 6 * t + 3
            a = cursor[lo:lo + 3]
            nxt[k:k + 3] = add192(a, mul192(pj, add192(a, cursor[hi:hi + 3])))
        cursor = nxt
        n = n // 2
    return cursor[0:3]


def sumcheck_round4(rd):
    # One PLAIN sumcheck round off the round record at `rd`, whose successor it
    # writes. The prover sends the round polynomial's coefficients bar the one the
    # split h(0) + h(1) == claim fixes, so the verifier derives that one and reads h
    # at the challenge by Horner. Nothing is reapplied: no eq factor, no separate
    # term for the tables still waiting, and the eq point is not read here at all.
    fs, c0, cursor = fs_next(rd[0:4], rd[GEN ** ROUND_CURSOR])
    fs, c2, cursor = fs_next(fs, cursor)
    fs, c3, cursor = fs_next(fs, cursor)
    c1 = add192(rd[ROUND_CLAIM:ROUND_CLAIM + 3], add192(c2, c3))  # the split fixes it, so it is neither sent nor bound
    fs, y = squeeze(fs)
    nxt = rd * GEN ** ROUND_SLOTS
    nxt[0:4] = fs
    nxt[GEN ** ROUND_CURSOR] = cursor
    nxt[ROUND_CLAIM:ROUND_CLAIM + 3] = add192(c0, mul192(y, add192(c1, mul192(y, add192(c2, mul192(y, c3))))))
    return y


def sumcheck_round5(rd, prev, challenge_out):
    # One GKR round off the round record at `rd`, whose successor it writes, its
    # challenge landing at `challenge_out`. The prover sends every coefficient but
    # c0, which the round's pulled-out eq factor (the challenge at `prev`) leaves
    # fixed: `c0 + prev_challenge * (c1 + ... + c4) == claim`.
    prev_challenge = prev[0:3]
    fs, c1, cursor = fs_next(rd[0:4], rd[GEN ** ROUND_CURSOR])
    fs, c2, cursor = fs_next(fs, cursor)
    fs, c3, cursor = fs_next(fs, cursor)
    fs, c4, cursor = fs_next(fs, cursor)
    fs, y = squeeze(fs)
    challenge_out[0:3] = y
    c0 = add192(rd[ROUND_CLAIM:ROUND_CLAIM + 3], mul192(prev_challenge, add192(add192(c1, c2), add192(c3, c4))))
    nxt = rd * GEN ** ROUND_SLOTS
    nxt[0:4] = fs
    nxt[GEN ** ROUND_CURSOR] = cursor
    nxt[ROUND_CLAIM:ROUND_CLAIM + 3] = add192(c0, mul192(y, add192(c1, mul192(y, add192(c2, mul192(y, add192(c3, mul192(y, c4))))))))
    return


def batch_sumcheck(fs: StackBuf(4), msgs, running: StackBuf(3), point, n_rounds: Const):
    # The rounds of a claim-batching sumcheck: two hinted values per round
    # (g(1) and g(inf)), the split fixing the third against the running claim, and
    # the challenges collected into `point`.
    for rd in unroll(0, n_rounds):
        fs, msg_g1, c = fs_next(fs, msgs * GEN ** (6 * rd))
        fs, msg_ginf, c = fs_next(fs, c)
        fs, rv = squeeze(fs)
        k = 3 * rd
        point[k:k + 3] = rv
        g_zero = add192(running, msg_g1)
        c_one = add192(g_zero, add192(msg_g1, msg_ginf))
        running = add192(mul192(add192(mul192(msg_ginf, rv), c_one), rv), g_zero)  # fold the degree-2 round at rv
    return fs, running


# ==================================== Merkle paths ==================================


@inline
def order_children(n0, n1, sibling, bit):
    # Branchless child ordering over two-word values: `bit` is boolean-pinned
    # wherever it comes from, so `m = bit*(node + sibling)` selects rather than
    # branches, leaving (node, sibling) at bit 0 and (sibling, node) at bit 1.
    m0 = bit * (n0 + sibling[0])
    m1 = bit * (n1 + sibling[1])
    return [n0 + m0, n1 + m1, sibling[0] + m0, sibling[1] + m1]


@inline
def verify_merkle_path(leaf, direction_bits, depth: Const):
    # Hinted child pairs are hashed in order; the boolean query bit selects the
    # child that must equal the running node, binding each link of the path.
    path = StackBuf(LIG_PATH_CAP)
    hint_witness(path[0:8 * depth], "merkle_children")
    path_ptr = addr(path)
    node = leaf
    for level in unroll(0, depth):
        dir_bit = direction_bits[GEN ** level]
        selected = path_ptr * GEN ** (8 * level) * (1 + dir_bit * (1 + GEN ** 4))
        selected[0:4] = node
        parent = StackBuf(4)
        blake2s(path[8 * level:8 * level + 4], path[8 * level + 4:8 * level + 8], parent)
        node = parent
    return node


@inline
def hash_cap_node(cap, index):
    # Node n of a cap occupies words 4n..4n+4, so its children start at 8n.
    children = cap * index ** 8
    parent = cap * index ** 4
    blake2s(children[0:4], children[4:8], parent[0:4])
    return


def verify_merkle_cap(cap, flags, depth: Const):
    if depth != 0:
        hash_cap_node(cap, GEN)
        flags[GEN] = 1
        for parent in mul_range(GEN, GEN ** (2 ** (depth - 1))):
            for side in unroll(0, 2):
                child = parent * parent * GEN ** side
                if flags[child] != 0:
                    flags[parent] = 1  # every active node forces its parent to be hashed
                    hash_cap_node(cap, child)
    return cap[4:8]


# ============================== the stacked WHIR opening ============================


def opening_fold(fs: StackBuf(4), cursor, c0: StackBuf(3), c1: StackBuf(3), c2: StackBuf(3)):
    fs, r = squeeze(fs)
    claim = add192(mul192(add192(mul192(c2, r), c1), r), c0)
    fs, n0, cursor = fs_next(fs, cursor)
    fs, n2, cursor = fs_next(fs, cursor)
    return fs, cursor, claim, n0, n2, r


def opening_ood_point(fs: StackBuf(4), point, n_g):
    # Share the squeeze loop across point dimensions.
    states = HeapBuf((n_g * GEN) ** FS_SLOTS)
    states[0:4] = fs
    for x in mul_range(1, n_g):
        state = states * x ** FS_SLOTS
        nb, r = squeeze(state[0:4])
        x3 = x ** 3
        point[x3:x3 + 3] = r
        state[4:8] = nb
    last = states * n_g ** FS_SLOTS
    return last[0:4]


def opening_final_message(fs: StackBuf(4), cursor, out, n: Const):
    for i in unroll(0, n):
        fs, value, cursor = fs_next(fs, cursor)
        k = 3 * i
        out[k:k + 3] = value
    return fs, cursor


def opening_queries(cap, flags, query_weights, query_bit_ptrs, fold_point, n_queries_g, base: Const, folds: Const, blocks: Const, depth: Const, cap_depth: Const):
    # Specialize by row and path shape so opening configurations share query code.
    # A row enters its level's claim through its multilinear extension at the
    # level's fold point, folded one coordinate at a time. At level 0, slot i of a
    # leaf image is interleaving index n-1-i (see open_stacked), which complements
    # every index bit, so a fold there keeps the high half's term.
    query_sum_chain = HeapBuf((n_queries_g * GEN) ** 3)
    query_sum_chain[0:3] = ZERO
    for xe in mul_range(1, n_queries_g):
        interleave = 2 ** folds  # bound in the body, which captures names by value
        row = StackBuf(LIG_ROW_CAP)
        fold = StackBuf(3 * LIG_ROW_CAP)
        r0 = fold_point[0:3]
        if base == 1:
            # Level 0's lanes are words, so its first fold runs limb by limb.
            hint_witness(row[0:interleave], "merkle_leaf_rows")
            for t in unroll(0, interleave // 2):
                lo = row[2 * t]
                hi = row[2 * t + 1]
                d = lo + hi
                k = 3 * t
                fold[k:k + 3] = [hi + d * r0[0], d * r0[1], d * r0[2]]
        else:
            # A deeper row is `interleave` elements, three limbs each.
            hint_witness(row[0:3 * interleave], "merkle_leaf_rows")
            for t in unroll(0, interleave // 2):
                k = 3 * t
                lo = 6 * t
                a = row[lo:lo + 3]
                fold[k:k + 3] = add192(a, mul192(r0, add192(a, row[lo + 3:lo + 6])))
        # Fold c reads fold c-1's outputs and writes the next run of the buffer.
        for c in unroll(1, folds):
            rc = fold_point[3 * c:3 * c + 3]
            src = 3 * (interleave - interleave // 2 ** (c - 1))
            dst = 3 * (interleave - interleave // 2 ** c)
            for t in unroll(0, interleave // 2 ** (c + 1)):
                a = fold[src + 6 * t:src + 6 * t + 3]
                b = fold[src + 6 * t + 3:src + 6 * t + 6]
                if base == 1:
                    fold[dst + 3 * t:dst + 3 * t + 3] = add192(b, mul192(rc, add192(a, b)))
                else:
                    fold[dst + 3 * t:dst + 3 * t + 3] = add192(a, mul192(rc, add192(a, b)))
        dot_at = 3 * (interleave - 2)
        row_dot = fold[dot_at:dot_at + 3]
        # The row's words are its leaf's byte image, hashed as full BLAKE2s blocks.
        leaf_state = StackBuf(4)
        blake2s(row[0:4], row[4:8], leaf_state, counter=64, final=1 // blocks)
        for jb in unroll(1, blocks):
            leaf_digest = StackBuf(4)
            blake2s(row[8 * jb:8 * jb + 4], row[8 * jb + 4:8 * jb + 8], leaf_digest, cv=leaf_state, counter=64 * (jb + 1), final=(jb + 1) // blocks)
            leaf_state = leaf_digest
        xe3 = xe ** 3
        nxt = xe3 * GEN ** 3
        query_sum_chain[nxt:nxt + 3] = add192(query_sum_chain[xe3:xe3 + 3], mul192(query_weights[xe3:xe3 + 3], row_dot))
        direction_bits = query_bit_ptrs[xe]
        path_depth = depth - cap_depth
        node = verify_merkle_path(leaf_state, direction_bits, path_depth)
        if cap_depth != 0:
            parent = GEN ** (2 ** (cap_depth - 1))
            for bit in unroll(0, cap_depth - 1):
                parent *= 1 + direction_bits[GEN ** (path_depth + 1 + bit)] * (1 + GEN ** (2 ** bit))
            flags[parent] = 1  # the cap check propagates this obligation to the root
            cap_index = parent * parent * (1 + direction_bits[GEN ** path_depth] * (1 + GEN))
        else:
            cap_index = GEN
        slot = cap * cap_index ** 4
        slot[0:4] = node
    end = n_queries_g ** 3
    return query_sum_chain[end:end + 3]


@inline
def fold_at(point, f: Const, lane_folds: Const, tail_start: Const):
    # Where fold challenge f (in round order) sits in the witness-order point: the
    # lane folds after the tail, every later fold `lane_folds` places down.
    if const(f // lane_folds == 0):
        pos = tail_start + f
    else:
        pos = f - lane_folds
    return point * GEN ** (3 * pos)


def open_stacked(m_idx: Const, fs: StackBuf(4), target: StackBuf(3), commit_root: StackBuf(4), cursor):
    # The stacked WHIR opening, one specialization per (rate, committed log-size)
    # candidate: every LIG_* table reads row m_idx, per level row `ml`, and all
    # opening proof data is hinted here, so only the executed arm pops its streams.
    #
    # The returned point is in witness order. The folds bind coordinates in ROUND
    # order, and level 0's folds are the lane fold, binding the witness's TOP k
    # coordinates: lane l of the commitment is the stack block q[l * 2^(mu-k) ...],
    # which is what makes the witness's zero padding whole lanes for the committer
    # to leave out of the encode. Every transparent weight downstream is written in
    # witness coordinates, so each challenge is written straight to its witness
    # coordinate as it arrives (`fold_at`), and the round-order readers below index
    # it there.
    n_levels = LIG_N_LEVELS[m_idx]
    yr_level = LIG_YR_LEVEL[m_idx]
    yr_log = LIG_YR_LOG_LEN[m_idx]
    yr_len = LIG_YR_LEN[m_idx]
    n_folds = LIG_TOTAL_FOLDS[m_idx]
    max_q = LIG_MAX_QUERIES[m_idx]
    ood_stride = LIG_MAX_OOD_SAMPLES * OOD_SLOTS
    lane_folds = LIG_FOLDS[m_idx * LIG_MAX_LEVELS]
    fold_head = n_folds - lane_folds
    tail_start = fold_head + yr_log
    # Padding is zero so shared prefix chains may compute unused entries above m
    # without reading uninitialized cells.
    point = HeapBuf(3 * (SIZE_BITS + SLOT_STRIDE_LOG))
    for j in unroll(n_folds + yr_log, SIZE_BITS + SLOT_STRIDE_LOG):
        k = 3 * j
        point[k:k + 3] = ZERO
    tail = point * GEN ** (3 * fold_head)

    # The opening's scalars (sumcheck messages, level roots, nonces, final message)
    # ride the SHARED stream, walked on in protocol order. The K opener binds a
    # Merkle root as two scalars, one per 128-bit half.
    msg_cursor = cursor
    fs, round_quad_c, msg_cursor = fs_next(fs, msg_cursor)  # the round polynomial in coefficients
    fs, round_quad_a, msg_cursor = fs_next(fs, msg_cursor)  # bar the linear one, which the split fixes
    round_quad_b = add192(target, round_quad_a)
    sumcheck_target = target

    # Caps are shared across queries, a node four words; rows and paths are hinted in
    # each query's frame.
    merkle_caps = HeapBuf(GEN ** (8 * LIG_CAP_LEN[m_idx]))
    hint_witness(merkle_caps[0:8 * LIG_CAP_LEN[m_idx]], "merkle_caps")
    cap_flags = HeapBuf(GEN ** LIG_CAP_LEN[m_idx])
    hint_witness(cap_flags[0:LIG_CAP_LEN[m_idx]], "merkle_cap_active")
    final_msg = HeapBuf(GEN ** (3 * yr_len))  # filled from the stream at the last level
    # Each cap root is checked against its transcript-bound level root.
    level_roots = HeapBuf(GEN ** (4 * n_levels))
    level_roots[0:4] = commit_root
    # ...and guest-filled accumulators (one slot per level / per query):
    level_betas = HeapBuf(GEN ** (3 * n_levels))
    query_weights = HeapBuf(GEN ** (3 * n_levels * max_q))
    query_positions = HeapBuf(GEN ** (LIG_POSITIONS_LEN[m_idx]))
    query_bit_ptrs = HeapBuf(GEN ** (LIG_POSITIONS_LEN[m_idx]))
    # Explicit OOD claims bind every recursive Johnson-list commitment. L0 needs
    # none: the opening claim itself is its post-commit binding value. An OOD claim
    # is read before its level's query positions but batched after them (one
    # challenge per level), so its value and intro message wait here.
    ood_z = HeapBuf(GEN ** (3 * n_levels * LIG_MAX_OOD_SAMPLES * LIG_LOG_MSG_COLS_CAP))
    ood = HeapBuf(GEN ** (n_levels * ood_stride))

    for lvl in unroll(0, n_levels):
        ml = m_idx * LIG_MAX_LEVELS + lvl
        n_queries = LIG_QUERIES[ml]
        depth = LIG_TREE_DEPTH[ml]
        folds_off = LIG_FOLDS_OFF[ml]
        pos_off = LIG_POSITIONS_OFF[ml]
        for j in unroll(0, LIG_FOLDS[ml]):
            fs, msg_cursor, sumcheck_target, round_quad_c, round_quad_a, fold_challenge = opening_fold(fs, msg_cursor, round_quad_c, round_quad_b, round_quad_a)
            fc = fold_at(point, folds_off + j, lane_folds, tail_start)
            fc[0:3] = fold_challenge
            round_quad_b = add192(sumcheck_target, round_quad_a)

        if lvl == yr_level:
            fs, msg_cursor = opening_final_message(fs, msg_cursor, final_msg, yr_len)
        else:
            # A non-canonical half is rejected (merkle.rs `scalars_to_hash`), as
            # the commitment root was at its own read.
            fs, root_a, msg_cursor = fs_next_half(fs, msg_cursor)
            fs, root_b, msg_cursor = fs_next_half(fs, msg_cursor)
            k = 4 * lvl + 4
            level_roots[k:k + 2] = root_a[0:2]
            level_roots[k + 2:k + 4] = root_b[0:2]
            # OOD binding for the newly observed level-(lvl+1) commitment. The
            # random point has the just-folded witness dimension, namely this
            # level's message-column dimension.
            for os in unroll(0, LIG_OOD_SAMPLES[ml + 1]):
                oz = ood_z * GEN ** (3 * ((lvl + 1) * LIG_MAX_OOD_SAMPLES + os) * LIG_LOG_MSG_COLS_CAP)
                fs = opening_ood_point(fs, oz, GEN ** LIG_LOG_MSG_COLS[ml])
                sample = ood * GEN ** ((lvl + 1) * ood_stride + os * OOD_SLOTS)
                fs, ood_y, msg_cursor = fs_next(fs, msg_cursor)
                fs, ood_c0, msg_cursor = fs_next(fs, msg_cursor)
                fs, ood_c2, msg_cursor = fs_next(fs, msg_cursor)
                sample[OOD_Y:OOD_Y + 3] = ood_y
                sample[OOD_C0:OOD_C0 + 3] = ood_c0
                sample[OOD_C2:OOD_C2 + 3] = ood_c2  # the split fixes c1 = y + c2
        q_nonce = msg_cursor[0:3]  # raw transport scalar: bound by the DS_POW_NONCE absorb below
        msg_cursor = msg_cursor * GEN ** 3
        if LIG_QUERY_GRIND_BITS[ml] != 0:
            grind_check(fs, q_nonce, GEN ** LIG_QUERY_GRIND_BITS[ml])
        else:
            assert_eq192(q_nonce, ZERO)
        nonce_state = StackBuf(4)
        blake2s(fs, [q_nonce, DS_POW_NONCE], nonce_state)
        fs = nonce_state

        sqz = HeapBuf((GEN ** (LIG_MAX_SQUEEZES[m_idx] + 1)) ** FS_SLOTS)
        sqz[0:4] = fs
        for xs in mul_range(1, GEN ** LIG_SQUEEZES[ml]):
            # a loop body captures free names BY VALUE, so the compile-time aliases
            # are rebound here (m_idx and lvl are substituted literals)
            depth = LIG_TREE_DEPTH[m_idx * LIG_MAX_LEVELS + lvl]
            pos_off = LIG_POSITIONS_OFF[m_idx * LIG_MAX_LEVELS + lvl]
            row = sqz * xs ** FS_SLOTS
            nb, packed = squeeze(row[0:4])
            row[4:8] = nb
            query_ptr = xs ** (FIELD_BITS // depth)
            decode_query_bits(packed, query_positions * GEN ** pos_off * query_ptr, query_bit_ptrs * GEN ** pos_off * query_ptr, depth)
        sqz_end = sqz * (GEN ** LIG_SQUEEZES[ml]) ** FS_SLOTS
        fs = sqz_end[0:4]

        # One batching challenge for the level, drawn once every claim it batches is
        # fixed: its OOD claims above and these query positions. Claim tau of the
        # level is weighted lam^tau, the running claim keeping lam^0 (Annex B,
        # Protocol 1 step 1): query i is claim n_ood + 1 + i, so its weight splits
        # into lam^i here and the level scalar lam^(n_ood+1) below.
        fs, lam = squeeze(fs)
        lam_pow = ONE
        for i in unroll(0, n_queries):
            k = 3 * (lvl * max_q + i)
            query_weights[k:k + 3] = lam_pow
            lam_pow = mul192(lam_pow, lam)

        cap_depth = LIG_CAP_DEPTH[ml]
        cap = merkle_caps * GEN ** (8 * LIG_CAP_OFF[ml])
        flags = cap_flags * GEN ** LIG_CAP_OFF[ml]
        level_root = verify_merkle_cap(cap, flags, cap_depth)
        k = 4 * lvl
        level_roots[k:k + 4] = level_root

        level_query_sum = opening_queries(cap, flags, query_weights * GEN ** (3 * lvl * max_q), query_bit_ptrs * GEN ** pos_off, fold_at(point, folds_off, lane_folds, tail_start), GEN ** n_queries, 1 // (lvl + 1), LIG_FOLDS[ml], LIG_LEAF_BLOCKS[ml], depth, cap_depth)

        # Every level, including the last, ties its commitment in through an intro
        # message. The level's claims then enter the running one with powers of
        # `lam`: the OOD claims held above first, then this query batch.
        fs, intro_c0, msg_cursor = fs_next(fs, msg_cursor)
        fs, intro_c2, msg_cursor = fs_next(fs, msg_cursor)
        intro_c1 = add192(level_query_sum, intro_c2)  # the split fixes the linear coefficient
        if lvl == yr_level:
            beta_lvl = lam  # no OOD claim at the last level: no new oracle
        else:
            ood_scalar = lam
            for os in unroll(0, LIG_OOD_SAMPLES[ml + 1]):
                sample = ood * GEN ** ((lvl + 1) * ood_stride + os * OOD_SLOTS)
                ood_y = sample[OOD_Y:OOD_Y + 3]
                ood_c2 = sample[OOD_C2:OOD_C2 + 3]
                sample[OOD_BETA:OOD_BETA + 3] = ood_scalar
                round_quad_c = add192(round_quad_c, mul192(ood_scalar, sample[OOD_C0:OOD_C0 + 3]))
                round_quad_b = add192(round_quad_b, mul192(ood_scalar, add192(ood_y, ood_c2)))
                round_quad_a = add192(round_quad_a, mul192(ood_scalar, ood_c2))
                sumcheck_target = add192(sumcheck_target, mul192(ood_scalar, ood_y))
                ood_scalar = mul192(ood_scalar, lam)
            beta_lvl = ood_scalar
        k = 3 * lvl
        level_betas[k:k + 3] = beta_lvl
        round_quad_c = add192(round_quad_c, mul192(beta_lvl, intro_c0))
        round_quad_b = add192(round_quad_b, mul192(beta_lvl, intro_c1))
        round_quad_a = add192(round_quad_a, mul192(beta_lvl, intro_c2))
        sumcheck_target = add192(sumcheck_target, mul192(beta_lvl, level_query_sum))

    # ---- finish the sumcheck over the tail coordinates ----
    for j in unroll(0, yr_log - 1):
        fs, msg_cursor, sumcheck_target, round_quad_c, round_quad_a, tail_c = opening_fold(fs, msg_cursor, round_quad_c, round_quad_b, round_quad_a)
        k = 3 * j
        tail[k:k + 3] = tail_c
        round_quad_b = add192(sumcheck_target, round_quad_a)
    # The closing round sends no following message.
    fs, tail_last = squeeze(fs)
    k = 3 * (yr_log - 1)
    tail[k:k + 3] = tail_last
    sumcheck_target = add192(round_quad_c, mul192(tail_last, add192(round_quad_b, mul192(tail_last, round_quad_a))))

    yr_at_tail = fold_final_msg(final_msg, tail, yr_log)

    # ---- per-level induced bases at the single terminal point ----
    # Every query of a level runs the SAME product shape over its message-column
    # coordinates; only the novel-basis chain (the query position's
    # subspace-vanishing walk, in F64) differs. Since
    #     1 + c_t * (1 + chain_t * inv_t) == (1 + c_t) + (c_t * inv_t) * chain_t
    # a coordinate's two coefficients depend on the challenge and the baked
    # vanishing inverse alone, so they hoist out of the query loop (one row a level,
    # fold coords then tail coords) and each query is one multiply-add a
    # coordinate.
    basis_a = HeapBuf(GEN ** (3 * n_levels * LIG_LOG_MSG_COLS_CAP))
    basis_b = HeapBuf(GEN ** (3 * n_levels * LIG_LOG_MSG_COLS_CAP))
    for lvl in unroll(0, n_levels):
        ml = m_idx * LIG_MAX_LEVELS + lvl
        prefix_len = LIG_RESIDUAL_PREFIX_LEN[ml]
        vanish = m_idx * LIG_MAX_VANISH_LEN + LIG_VANISH_OFF[ml]
        for t in unroll(0, prefix_len):
            fold_c = fold_at(point, LIG_RESIDUAL_FOLD_OFF[ml] + t, lane_folds, tail_start)
            dst = 3 * (lvl * LIG_LOG_MSG_COLS_CAP + t)
            basis_a[dst:dst + 3] = add192(ONE, fold_c[0:3])
            basis_b[dst:dst + 3] = scale(LIG_VANISH_INVS[vanish + t], fold_c[0:3])
        for j in unroll(0, yr_log):
            src = 3 * j
            tail_c = tail[src:src + 3]
            dst = 3 * (lvl * LIG_LOG_MSG_COLS_CAP + prefix_len + j)
            basis_a[dst:dst + 3] = add192(ONE, tail_c)
            basis_b[dst:dst + 3] = scale(LIG_VANISH_INVS[vanish + prefix_len + j], tail_c)
    inner_chain = HeapBuf(GEN ** (3 * (n_levels + 1)))
    inner_chain[0:3] = ZERO
    for lvl in unroll(0, n_levels):
        ml = m_idx * LIG_MAX_LEVELS + lvl
        residual_chain = HeapBuf(GEN ** (3 * (max_q + 1)))
        residual_chain[0:3] = ZERO
        for xr in mul_range(1, GEN ** LIG_QUERIES[ml]):
            ml = m_idx * LIG_MAX_LEVELS + lvl  # rebound: the body captures by value
            vanish = m_idx * LIG_MAX_VANISH_LEN + LIG_VANISH_OFF[ml]
            basis_row = lvl * LIG_LOG_MSG_COLS_CAP
            max_q = LIG_MAX_QUERIES[m_idx]
            basis_chain = query_positions[GEN ** LIG_POSITIONS_OFF[ml] * xr]
            b0 = 3 * basis_row
            prefix_eq = add192(basis_a[b0:b0 + 3], scale(basis_chain, basis_b[b0:b0 + 3]))
            for t in unroll(1, LIG_LOG_MSG_COLS[ml]):
                # subspace-vanishing recurrence for the novel-basis point
                basis_chain *= (basis_chain + LIG_VANISH_VALS[vanish + t - 1])
                bt = 3 * (basis_row + t)
                prefix_eq = mul192(prefix_eq, add192(basis_a[bt:bt + 3], scale(basis_chain, basis_b[bt:bt + 3])))
            xr3 = xr ** 3
            nxt = xr3 * GEN ** 3
            qw = GEN ** (3 * lvl * max_q) * xr3
            residual_chain[nxt:nxt + 3] = add192(residual_chain[xr3:xr3 + 3], mul192(query_weights[qw:qw + 3], prefix_eq))
        # accumulate beta_lvl * (per-level residual sum) into the grand residual
        end = GEN ** (3 * LIG_QUERIES[ml])
        k = 3 * lvl
        inner_chain[k + 3:k + 6] = add192(inner_chain[k:k + 3], mul192(level_betas[k:k + 3], residual_chain[end:end + 3]))

    # Explicit OOD eq bases at the same terminal point.
    ood_inner = ZERO
    for ood_lvl in unroll(1, n_levels):
        ml = m_idx * LIG_MAX_LEVELS + ood_lvl
        z_folded = LIG_LOG_MSG_COLS[ml - 1] - yr_log
        ris_start = LIG_FOLDS_OFF[ml]
        for os in unroll(0, LIG_OOD_SAMPLES[ml]):
            oz = ood_z * GEN ** (3 * (ood_lvl * LIG_MAX_OOD_SAMPLES + os) * LIG_LOG_MSG_COLS_CAP)
            sample = ood * GEN ** (ood_lvl * ood_stride + os * OOD_SLOTS)
            scalar = sample[OOD_BETA:OOD_BETA + 3]
            for t in unroll(0, z_folded):
                zk = 3 * t
                fc = fold_at(point, ris_start + t, lane_folds, tail_start)
                scalar = mul192(scalar, add192(ONE, add192(oz[zk:zk + 3], fc[0:3])))
            for t in unroll(0, yr_log):
                zk = 3 * (z_folded + t)
                tk = 3 * t
                scalar = mul192(scalar, add192(ONE, add192(oz[zk:zk + 3], tail[tk:tk + 3])))
            ood_inner = add192(ood_inner, scalar)
    inner_end = 3 * n_levels
    return sumcheck_target, point, add192(inner_chain[inner_end:inner_end + 3], ood_inner), yr_at_tail


# ============================== inner-proof verification ============================
# The phases of `verify_sub`, in the order it runs them. Each takes and returns the
# Fiat-Shamir state and the stream cursor, so the sequence is what binds them.


def verify_bus_gkr(fs: StackBuf(4), cursor, g_bus_mu, zeta):
    # ONE GKR grand product over push, pull and count, RLC-batched. Push and pull
    # have equal depth (matched blocks) and the count tree is padded with identity
    # leaves up to it (product unchanged), so a single sumcheck serves all three.
    # Radix four contracts two binary levels per layer; after checking the combined
    # product identity, a fresh λ pins the individual values. All three trees reduce
    # to the one shared point `zeta`, which this fills, returning their three leaf
    # values with the walked Fiat-Shamir state and stream cursor.
    layers = HeapBuf((g_bus_mu * GEN ** 2) ** LAYER_SLOTS)  # mu + 2 layers
    rounds = HeapBuf(GKR_ROUNDS_CAP * ROUND_SLOTS)
    gkr_pts = HeapBuf(3 * GKR_POINTS_CAP)
    assert log(g_bus_mu) < COUNT_BITS
    fs, root_push, cursor = fs_next(fs, cursor)
    fs, root_count, cursor = fs_next(fs, cursor)
    assert_ne192(root_count, ZERO)  # count-tree root nonzero: no read count self-cancels
    fs, root_lambda = squeeze(fs)
    layers[0:4] = fs
    layers[GEN ** LAYER_CURSOR] = cursor
    layers[LAYER_PUSH:LAYER_PUSH + 3] = root_push
    layers[LAYER_PULL:LAYER_PULL + 3] = root_push
    layers[LAYER_COUNT:LAYER_COUNT + 3] = root_count
    layers[LAYER_LAMBDA:LAYER_LAMBDA + 3] = root_lambda  # λ over the three roots
    layers[GEN ** LAYER_ROW] = gkr_pts
    layers[GEN ** LAYER_POS] = GEN ** 0

    # Contract two binary product levels at a time. pair_bounds[g^d] = g^(d//2) is
    # the radix-four layer count, and shift is g exactly when the depth is odd, in
    # which case the root-most BINARY layer runs first.
    pair_bounds = HeapBuf(COUNT_BITS)
    depth_shift = HeapBuf(COUNT_BITS)
    for depth in unroll(0, COUNT_BITS):
        pair_bounds[GEN ** depth] = GEN ** (depth // 2)
        depth_shift[GEN ** depth] = GEN ** (depth % 2)

    if depth_shift[g_bus_mu] != 1:
        # The odd layer is layer 0, so its round state would be written and read
        # back at the same position: read it straight off the layer instead.
        lam = layers[LAYER_LAMBDA:LAYER_LAMBDA + 3]
        tail_fs = layers[0:4]
        tcur = layers[GEN ** LAYER_CURSOR]
        tclaim = add192(layers[LAYER_PUSH:LAYER_PUSH + 3], mul192(lam, add192(layers[LAYER_PULL:LAYER_PULL + 3], mul192(lam, layers[LAYER_COUNT:LAYER_COUNT + 3]))))
        nextrow = gkr_pts * GEN ** (3 * MU_CAP)
        evals = StackBuf(3 * 2 * N_GKR_SIDES)  # the two children of each side, in side order
        for i in unroll(0, 2 * N_GKR_SIDES):
            tail_fs, ev, tcur = fs_next(tail_fs, tcur)
            k = 3 * i
            evals[k:k + 3] = ev
        combined = ZERO
        for i in unroll(0, N_GKR_SIDES):
            side = N_GKR_SIDES - 1 - i  # Horner in lam, so the top side lands last
            k = 6 * side
            combined = add192(mul192(evals[k:k + 3], evals[k + 3:k + 6]), mul192(lam, combined))
        assert_eq192(tclaim, combined)
        tail_fs, c0 = squeeze(tail_fs)
        nextrow[0:3] = c0
        tail_fs, tail_lambda = squeeze(tail_fs)  # fresh λ pins the tail individuals
        nxt = layers * GEN ** LAYER_SLOTS
        nxt[0:4] = tail_fs
        nxt[GEN ** LAYER_CURSOR] = tcur
        for side in unroll(0, N_GKR_SIDES):
            k = 6 * side
            out = LAYER_PUSH + 3 * side
            ev_lo = evals[k:k + 3]
            nxt[out:out + 3] = add192(ev_lo, mul192(c0, add192(ev_lo, evals[k + 3:k + 6])))
        nxt[LAYER_LAMBDA:LAYER_LAMBDA + 3] = tail_lambda
        nxt[GEN ** LAYER_ROW] = nextrow
        nxt[GEN ** LAYER_POS] = GEN

    for x_pair in mul_range(1, pair_bounds[g_bus_mu]):
        x_layer = x_pair * x_pair * depth_shift[g_bus_mu]
        layer = layers * x_layer ** LAYER_SLOTS
        lam = layer[LAYER_LAMBDA:LAYER_LAMBDA + 3]
        point_row = layer[GEN ** LAYER_ROW]
        round_pos = layer[GEN ** LAYER_POS]
        nextrow = point_row * GEN ** (3 * MU_CAP)
        head = rounds * round_pos ** ROUND_SLOTS
        head[0:4] = layer[0:4]
        head[GEN ** ROUND_CURSOR] = layer[GEN ** LAYER_CURSOR]
        head[ROUND_CLAIM:ROUND_CLAIM + 3] = add192(layer[LAYER_PUSH:LAYER_PUSH + 3], mul192(lam, add192(layer[LAYER_PULL:LAYER_PULL + 3], mul192(lam, layer[LAYER_COUNT:LAYER_COUNT + 3]))))
        for x_round in mul_range(1, x_layer):
            xr3 = x_round ** 3
            sumcheck_round5(rounds * (round_pos * x_round) ** ROUND_SLOTS, point_row * xr3, nextrow * xr3 * GEN ** 6)
        tail = rounds * (round_pos * x_layer) ** ROUND_SLOTS
        tail_fs = tail[0:4]
        tcur = tail[GEN ** ROUND_CURSOR]
        tclaim = tail[ROUND_CLAIM:ROUND_CLAIM + 3]
        evals = StackBuf(3 * 4 * N_GKR_SIDES)  # the four children of each side, in side order
        for i in unroll(0, 4 * N_GKR_SIDES):
            tail_fs, ev, tcur = fs_next(tail_fs, tcur)
            k = 3 * i
            evals[k:k + 3] = ev
        combined = ZERO
        for i in unroll(0, N_GKR_SIDES):
            side = N_GKR_SIDES - 1 - i  # Horner in lam, so the top side lands last
            k = 12 * side
            combined = add192(mul192(mul192(evals[k:k + 3], evals[k + 3:k + 6]), mul192(evals[k + 6:k + 9], evals[k + 9:k + 12])), mul192(lam, combined))
        assert_eq192(tclaim, combined)
        tail_fs, c0 = squeeze(tail_fs)
        tail_fs, c1 = squeeze(tail_fs)
        nextrow[0:3] = c0
        nextrow[3:6] = c1
        tail_fs, tail_lambda = squeeze(tail_fs)
        nxt = layer * GEN ** (2 * LAYER_SLOTS)
        nxt[0:4] = tail_fs
        nxt[GEN ** LAYER_CURSOR] = tcur
        for side in unroll(0, N_GKR_SIDES):
            k = 12 * side
            out = LAYER_PUSH + 3 * side
            e0 = evals[k:k + 3]
            e2 = evals[k + 6:k + 9]
            lo = add192(e0, mul192(c0, add192(e0, evals[k + 3:k + 6])))
            hi = add192(e2, mul192(c0, add192(e2, evals[k + 9:k + 12])))
            nxt[out:out + 3] = add192(lo, mul192(c1, add192(lo, hi)))
        nxt[LAYER_LAMBDA:LAYER_LAMBDA + 3] = tail_lambda
        nxt[GEN ** LAYER_ROW] = nextrow
        nxt[GEN ** LAYER_POS] = round_pos * x_layer * GEN
    last = layers * g_bus_mu ** LAYER_SLOTS
    final_point_row = last[GEN ** LAYER_ROW]
    for xt in mul_range(1, g_bus_mu):
        x3 = xt ** 3
        zeta[x3:x3 + 3] = final_point_row[x3:x3 + 3]  # the ONE shared point
    return last[0:4], last[GEN ** LAYER_CURSOR], last[LAYER_PUSH:LAYER_PUSH + 3], last[LAYER_PULL:LAYER_PULL + 3], last[LAYER_COUNT:LAYER_COUNT + 3]


def verify_tables(fs: StackBuf(4), cursor, pi: StackBuf(4), zeta, g_bus_mu, dims_g, block_kappa, g_squares, fp_w, beta: StackBuf(3), claim_pool, claim_cplen_g, chi, claim_push: StackBuf(3), claim_pull: StackBuf(3), claim_count: StackBuf(3)):
    # Settle the bus against the eight tables, in four steps: certify each side's
    # leaf-cube tiling, decompose the three GKR leaf values over it, run the ONE
    # table sumcheck they all reduce to, and bind the public input. Pooled claims
    # land in claim_pool/claim_cplen_g and the reduced point in `chi`; the batch's
    # round count g^n, the deferred bytecode share and the PI point come back.
    #
    # Bus-leaf packing offsets, for the selector certification. Each side's blocks
    # tile its leaf cube, block b at offset_b; the hinted order is only
    # PERMUTATION-checked and offsets accumulate as g^offset = Π_{earlier} g^(2^κ).
    # The decompose below pins each block's selector bits against this offset,
    # forcing κ-alignment, and no sort or tie-break check is needed: alignment plus
    # consecutive offsets force a valid tiling, and the grand product is
    # position-independent, so any tiling is sound. Pull's blocks mirror push's and
    # share zeta, so only push and count need offsets (pull's slots go unread).
    sort_order = HeapBuf(N_BLOCKS)
    hint_witness(sort_order[0:N_BLOCKS], "sort_order")
    block_side_tab = HeapBuf(N_BLOCKS)  # global block -> its side
    for b in unroll(0, N_BLOCKS):
        block_side_tab[GEN ** b] = BLOCK_SIDE[b]
    block_off_g = HeapBuf(N_BLOCKS)  # g^offset per block, keyed by global index
    for cert in unroll(0, 2):
        s = COUNT_SIDE * cert  # PUSH_SIDE (0), then COUNT_SIDE (2)
        g_off = GEN ** 0
        for r in unroll(SIDE_BLOCK_START[s], SIDE_BLOCK_START[s + 1]):
            global_g = sort_order[GEN ** r]       # g^{global block index at this rank}
            assert log(global_g) < N_BLOCKS       # a valid block index
            assert block_side_tab[global_g] == s  # ...belonging to THIS side
            # write-once: a repeat collides, and an omission fails the decompose's
            # offset read below
            block_off_g[global_g] = g_off
            g_off *= g_squares[block_kappa[global_g]]

    # ---- 3x leaf decomposition (claims pooled; bytecode Public DEFERRED) ----
    # Reconstruct Ṽ₀(ζ) per side and assert it equals the GKR leaf value. The
    # committed-coordinate values ride the stream (observed, pooled); Index
    # coordinates use the factored index MLE; and the program's whole share of a
    # bytecode leaf is ONE evaluation of the stacked polynomial, since its slots are
    # aligned with the tuple and the weights are eq(α⃗, ·), so the share IS that
    # polynomial at (ζ_lo, α⃗) (doc sec:e2e-bc): one hinted value, exported as a
    # deferred claim, with no per-coordinate values and no selector challenge.
    #
    # Pull's blocks mirror push's (same kappas, same offsets, generator-asserted
    # pairing) and share zeta, so each pull block REUSES its push twin's eq_hi and
    # Index-MLE value instead of recomputing them; its column values are mostly
    # deduped pool reads (COORD_FRESH). The identity check against pull's own GKR
    # claim still binds everything.
    bc_share = StackBuf(3)
    hint_witness(bc_share, "bytecode_val")
    idxc_tab = HeapBuf(SIZE_BITS)  # INDEX_MLE_FACTORS[t] = 1 + g^(2^t)
    for t in unroll(0, SIZE_BITS):
        idxc_tab[GEN ** t] = INDEX_MLE_FACTORS[t]
    bus_table_total = StackBuf(3 * N_GKR_SIDES)  # per side, what its tables' blocks owe
    block_eq_hi = StackBuf(3 * N_BLOCKS)         # every block's eq_hi, reused below
    block_index_mle = HeapBuf(3 * N_BLOCKS)      # per push block with an Index coord
    for s in unroll(0, N_GKR_SIDES):
        acc = ZERO
        selector_sum = ZERO
        for b in unroll(SIDE_BLOCK_START[s], SIDE_BLOCK_START[s + 1]):
            block_has_public = 0
            kappa_g = block_kappa[GEN ** b]
            assert log(kappa_g) < SIZE_BITS
            if s == PULL_SIDE:
                twin = 3 * (b - SIDE_BLOCK_START[PULL_SIDE])
                eq_hi = block_eq_hi[twin:twin + 3]
            else:
                # eq_hi over the ζ coords above κ against the selector bits, whose
                # run is mu_s − κ = g^mu_s / g^κ long. Selector bits = offset >> κ:
                # advice-decompose the offset and read it shifted by κ. Rebuilding
                # g^offset from those high bits alone (weights g^(2^(κ+k))) and
                # asserting it equals block_off_g pins the bits AND the κ-alignment
                # in one shot; the low κ bit cells are written but never read.
                sel_len_g = g_bus_mu / kappa_g  # g^(mu - κ)
                assert log(sel_len_g) < SIZE_BITS
                zeta_hi = zeta * kappa_g ** 3
                offset_bits = HeapBuf(GEN ** SIZE_BITS)
                hint_decompose_bits_exponent(offset_bits, block_off_g[GEN ** b], SIZE_BITS)
                sel_bits = offset_bits * kappa_g
                eq_chain = HeapBuf(3 * (MU_CAP + 2))
                goff_chain = HeapBuf(MU_CAP + 2)  # rebuild g^offset from the high bits
                eq_chain[0:3] = ONE
                goff_chain[GEN ** 0] = 1
                for xk in mul_range(1, sel_len_g):
                    sbit = sel_bits[xk]
                    sel_bits[xk] = sbit * sbit  # booleanity as a write-once pin
                    x3 = xk ** 3
                    nxt = x3 * GEN ** 3
                    eq_chain[nxt:nxt + 3] = mul192(eq_chain[x3:x3 + 3], add64(zeta_hi[x3:x3 + 3], 1 + sbit))  # eq over GF(2) is 1 + b + z
                    goff_chain[xk * GEN] = goff_chain[xk] * (1 + sbit * (g_squares[kappa_g * xk] + 1))
                sel_end = sel_len_g ** 3
                eq_hi = eq_chain[sel_end:sel_end + 3]
                assert goff_chain[sel_len_g] == block_off_g[GEN ** b]  # bits == offset >> κ, κ-aligned
            selector_sum = add192(selector_sum, eq_hi)
            bk = 3 * b
            block_eq_hi[bk:bk + 3] = eq_hi
            # A TABLE's block streams no value here: the table sumcheck settles its
            # fingerprint from that table's column evaluations. Only the framework
            # blocks (boundary, memory, bytecode) still decompose.
            if BLOCK_TABLE[b] == NO_TABLE:
                # inner fingerprint Σ_i w_i · coord_i(ζ_lo); the count side weighs
                # slot 0 alone (α⃗ = 0), γ = 0.
                inner_sum = ZERO
                for i in unroll(0, BLOCK_COORD_COUNT[b]):
                    ci = BLOCK_COORD_OFF[b] + i  # a compile-time index, so `ci` costs nothing
                    coord_val = ZERO
                    slot = 3 * COORD_CLAIM_SLOT[ci]
                    if COORD_TYPE[ci] == COORD_KIND_CONST:
                        coord_val = f192(COORD_CONST[ci], 0, 0)
                    if COORD_TYPE[ci] == COORD_KIND_COL:
                        if COORD_FRESH[ci] == 1:
                            fs, coord_val, cursor = fs_next(fs, cursor)
                            claim_pool[slot:slot + 3] = coord_val
                            claim_cplen_g[GEN ** COORD_CLAIM_SLOT[ci]] = kappa_g  # cplen = block kappa
                        else:
                            coord_val = claim_pool[slot:slot + 3]
                    if COORD_TYPE[ci] == COORD_KIND_GCOL:
                        if COORD_FRESH[ci] == 1:
                            fs, rawv, cursor = fs_next(fs, cursor)
                            claim_pool[slot:slot + 3] = rawv
                            claim_cplen_g[GEN ** COORD_CLAIM_SLOT[ci]] = kappa_g
                        else:
                            rawv = claim_pool[slot:slot + 3]
                        coord_val = scale(COORD_CONST[ci], rawv)
                    if COORD_TYPE[ci] == COORD_KIND_INDEX:
                        if s == PULL_SIDE:
                            twin = 3 * (b - SIDE_BLOCK_START[PULL_SIDE])
                            coord_val = block_index_mle[twin:twin + 3]
                        else:
                            # Index-coord MLE: prod_t (1 + zeta_t * (1 + g^(2^t)))
                            idx_chain = HeapBuf(3 * (MU_CAP + 2))
                            idx_chain[0:3] = ONE
                            for xt in mul_range(1, kappa_g):
                                x3 = xt ** 3
                                nxt = x3 * GEN ** 3
                                idx_chain[nxt:nxt + 3] = mul192(idx_chain[x3:x3 + 3], add64(scale(idxc_tab[xt], zeta[x3:x3 + 3]), 1))
                            idx_end = kappa_g ** 3
                            coord_val = idx_chain[idx_end:idx_end + 3]
                            if s == PUSH_SIDE:
                                block_index_mle[bk:bk + 3] = coord_val
                    if COORD_TYPE[ci] == COORD_KIND_PUBLIC:
                        # The public slots carry no value of their own here: their
                        # alpha-weighted sum IS bc_share, added once per block below
                        # (push and pull share zeta, so both get the same one).
                        block_has_public = 1
                    if s == COUNT_SIDE:
                        inner_sum = add192(inner_sum, coord_val)
                    else:
                        wk = 3 * i
                        inner_sum = add192(inner_sum, mul192(fp_w[wk:wk + 3], coord_val))
                if block_has_public == 1:
                    inner_sum = add192(inner_sum, bc_share)  # the bytecode blocks' public slots
                if s == COUNT_SIDE:
                    acc = add192(acc, mul192(eq_hi, inner_sum))
                else:
                    acc = add192(acc, mul192(eq_hi, add192(beta, inner_sum)))
        acc = add64(add192(acc, selector_sum), 1)
        # What the tables' blocks owe this side: its GKR leaf value less the
        # framework decomposition. DERIVED, not read: a transmitted total would be a
        # free value in its own check. The table sumcheck's target pins it below.
        if s == PUSH_SIDE:
            leaf = claim_push
        if s == PULL_SIDE:
            leaf = claim_pull
        if s == COUNT_SIDE:
            leaf = claim_count
        sk = 3 * s
        bus_table_total[sk:sk + 3] = add192(acc, leaf)
    claim_idx = N_BUS_CLAIMS  # table and PI claims pool after the deduped bus claims

    # ---- ONE table sumcheck for all eight tables ----
    # Mirrors lean_vm::constraints::verify. zc_xi ONCE, each table folding its own
    # identities with a DISJOINT range of its powers (ETA_OFFSET[t]); one shared
    # point zeta (the bus GKR's); n = max_t tau_t rounds. Rounds bind the HIGHEST
    # variable first, so a 2^tau table sits out the first n - tau and joins carrying
    # the challenges it sat out, weighing cprod[n - tau] * peq[tau] where peq[tau] =
    # eq(zeta[..tau], chi[..tau]); the zc_xi-powers are inside constraint_eval.
    #
    # g^n is hinted, then pinned exactly: the range-checked division slacks force it
    # to dominate every certified tau and the product identity forces it to BE one.
    g_zc_n = hint_witness("zc_tau_max")
    zc_is_a_tau = 1
    for t in unroll(0, N_TABLES):
        tau_g = dims_g[GEN ** (t + 1)]
        assert log(g_zc_n / tau_g) < COUNT_BITS
        zc_is_a_tau *= g_zc_n + tau_g
    assert zc_is_a_tau == 0
    # n <= mu, the `Error::Truncated` of constraints.rs. Every table pushes at
    # kappa = tau, so it holds structurally, but zc_peq below reads zeta[..n] and
    # zeta only holds mu coords: unwritten heap there is prover-chosen.
    assert log(g_bus_mu / g_zc_n) < COUNT_BITS
    fs, zc_xi = squeeze(fs)
    zc_xi_pows = StackBuf(3 * N_ETA_POWS)
    zc_xi_pows[0:3] = ONE
    for k in unroll(1, N_ETA_POWS):
        c = 3 * k
        zc_xi_pows[c:c + 3] = mul192(zc_xi_pows[c - 3:c], zc_xi)
    # The eq point is the bus GKR's zeta, NOT a fresh one, which is what lets the
    # batch settle the bus forms alongside the constraints. It is also why no target
    # is read: what the three sides' tables owe, each in its own shared power of
    # zc_xi, IS the sum the batch must reach, and zc_xi is squeezed after those
    # totals are fixed, so hitting one number forces all three side equations.
    bus_target = ZERO
    for sd in unroll(0, N_GKR_SIDES):
        e = 3 * (ETA_FORM_BASE + sd)
        k = 3 * sd
        bus_target = add192(bus_target, mul192(zc_xi_pows[e:e + 3], bus_table_total[k:k + 3]))
    # n vanilla sumcheck rounds: the round polynomial arrives whole, so a round is
    # `h(0) + h(1) == claim` and a fold, with no eq to reapply. The tables still
    # waiting ride inside h, so nothing here is indexed by height; the heights enter
    # only the per-table weights below.
    zc_rounds = HeapBuf((g_zc_n * GEN) ** ROUND_SLOTS)
    zc_cprod = HeapBuf((g_zc_n * GEN) ** 3)  # the challenges bound so far, multiplied
    zc_rounds[0:4] = fs
    zc_rounds[GEN ** ROUND_CURSOR] = cursor
    zc_rounds[ROUND_CLAIM:ROUND_CLAIM + 3] = bus_target
    zc_cprod[0:3] = ONE
    for xk in mul_range(1, g_zc_n):
        rk = sumcheck_round4(zc_rounds * xk ** ROUND_SLOTS)
        bound = (g_zc_n * INV_GEN / xk) ** 3  # g^(n-1-j): the variable round j binds
        chi[bound:bound + 3] = rk
        # cprod is the weight of a table that joins here; peq below is the rest
        x3 = xk ** 3
        nxt = x3 * GEN ** 3
        zc_cprod[nxt:nxt + 3] = mul192(zc_cprod[x3:x3 + 3], rk)
    zc_last = zc_rounds * g_zc_n ** ROUND_SLOTS
    fs = zc_last[0:4]
    cursor = zc_last[GEN ** ROUND_CURSOR]
    claim = zc_last[ROUND_CLAIM:ROUND_CLAIM + 3]
    # peq[g^tau] = eq(zeta[..tau], chi[..tau]), as a prefix chain.
    zc_peq = HeapBuf((g_zc_n * GEN) ** 3)
    eq_prefix_chain(zc_peq, ONE, zeta, chi, g_zc_n)
    # Per table: every committed column's evaluation (pooled), its AIR constraint
    # at its own reduced point chi[..tau_t], weighted into the batch's final claim.
    air_acc = ZERO
    for t in unroll(0, N_TABLES):
        tau_g = dims_g[GEN ** (t + 1)]
        col_evals = StackBuf(3 * TABLE_COLS_CAP)
        for k in unroll(0, N_TABLE_COLS[t]):
            fs, e, cursor = fs_next(fs, cursor)
            c = 3 * k
            col_evals[c:c + 3] = e
            p = 3 * claim_idx
            claim_pool[p:p + 3] = e
            claim_cplen_g[GEN ** claim_idx] = tau_g  # cplen = tau_t
            claim_idx += 1
        # The table's AIR constraint at the final point (col_evals is indexed by
        # local column index; the formulas mirror tables.rs eval_constraint). Every
        # value relation rides the bus as a degree-2 coordinate, so only JUMP's
        # is-nonzero indicator is left with an identity of its own.
        constraint_eval = ZERO
        if t == TABLE_JUMP:
            # `b = c*w` and `c*(b+1) = 0` (tables.rs jump_identity). Local columns:
            # v_cond at 5, w at 12, the indicator b at 13.
            cond = col_evals[15:18]
            indicator = col_evals[39:42]
            x0 = 3 * ETA_OFFSET[t]
            x1 = x0 + 3
            constraint_eval = add192(mul192(zc_xi_pows[x0:x0 + 3], add192(indicator, mul192(cond, col_evals[36:39]))), mul192(zc_xi_pows[x1:x1 + 3], mul192(cond, add192(indicator, ONE))))
        # The table's three bus forms, evaluated at the SAME column evaluations:
        # Σ_b eq_hi(b) · (γ + Σ_i α^i · coord_i), the coords read off col_evals at
        # their local index. This is what replaces opening those columns at ζ.
        for sd in unroll(0, N_GKR_SIDES):
            form = ZERO
            for b in unroll(0, N_BLOCKS):
                if BLOCK_SIDE[b] == sd:
                    if BLOCK_TABLE[b] == t:
                        inner = ZERO
                        for i in unroll(0, BLOCK_COORD_COUNT[b]):
                            # Each coord is the sum of its terms, over this table's
                            # column evaluations. A product term (an address, an
                            # arithmetic result) is degree 2, which the batch's
                            # round polynomial already allows.
                            ci = BLOCK_COORD_OFF[b] + i  # a compile-time index, so `ci` costs nothing
                            cv = ZERO
                            for j in unroll(0, COORD_TERM_COUNT[ci]):
                                tj = COORD_TERM_OFF[ci] + j
                                ca = 3 * TERM_COL_A[tj]
                                cb = 3 * TERM_COL_B[tj]
                                if TERM_TYPE[tj] == COORD_KIND_CONST:
                                    cv = add192(cv, f192(TERM_CONST[tj], 0, 0))
                                if TERM_TYPE[tj] == COORD_KIND_COL:
                                    cv = add192(cv, col_evals[ca:ca + 3])
                                if TERM_TYPE[tj] == COORD_KIND_GCOL:
                                    cv = add192(cv, scale(TERM_CONST[tj], col_evals[ca:ca + 3]))
                                if TERM_TYPE[tj] == COORD_KIND_PROD:
                                    cv = add192(cv, scale(TERM_CONST[tj], mul192(col_evals[ca:ca + 3], col_evals[cb:cb + 3])))
                            if sd == COUNT_SIDE:
                                inner = add192(inner, cv)
                            else:
                                wk = 3 * i
                                inner = add192(inner, mul192(fp_w[wk:wk + 3], cv))
                        bk = 3 * b
                        if sd == COUNT_SIDE:
                            form = add192(form, mul192(block_eq_hi[bk:bk + 3], inner))
                        else:
                            form = add192(form, mul192(block_eq_hi[bk:bk + 3], add192(beta, inner)))
            e = 3 * (ETA_FORM_BASE + sd)
            constraint_eval = add192(constraint_eval, mul192(zc_xi_pows[e:e + 3], form))
        joins = (g_zc_n / tau_g) ** 3
        sits = tau_g ** 3
        air_acc = add192(air_acc, mul192(mul192(zc_cprod[joins:joins + 3], zc_peq[sits:sits + 3]), constraint_eval))  # cprod[n - tau] * peq[tau]
    assert_eq192(air_acc, claim)

    # ---- public-input binding claim ----
    # The VM's bind_pi_claim: the committed MEM at (r0, r1, 0, ...) equals the
    # multilinear extension of the four public words at (r0, r1), low variable
    # first. Both sides know the words, so the value is computed and nothing rides
    # the stream.
    fs, r0 = squeeze(fs)
    fs, r1 = squeeze(fs)
    v_lo = add64(scale(pi[0] + pi[1], r0), pi[0])
    v_hi = add64(scale(pi[2] + pi[3], r0), pi[2])
    p = 3 * claim_idx
    claim_pool[p:p + 3] = add192(v_lo, mul192(r1, add192(v_lo, v_hi)))
    return fs, cursor, g_zc_n, bc_share, r0, r1


def verify_flock(fs: StackBuf(4), cursor, tau_blake2s_g, zerocheck_chis, lincheck_rs, z_partial):
    # Flock's zerocheck (univariate skip, k_skip = 6) then its lincheck, whose
    # matrix evaluation is DEFERRED to the caller's statement. The three run buffers
    # come in pre-sized; the point z, lincheck's alpha and the deferred matrix part
    # come back with the walked Fiat-Shamir state and stream cursor.
    #
    # tau's reach is bounded: the count gadget gives tau < 34 (every flock buffer is
    # sized for that), and q_flock's committed kappa = K_LOG + tau feeds the
    # certified size m, whose dispatch bound caps tau below any baked structure. The
    # first K_SKIP Boolean rounds are replaced by the univariate skip and consume no
    # equality challenges; the remaining r coordinates are N_FIXED_CHALLENGE_ROUNDS
    # fixed inner values then sampled outer ones. The prover builds round 1 from
    # this equality tail, so its sampled part is squeezed before round 1 is fetched,
    # and round 1 before z, which evaluates it.
    mr1cs_g = tau_blake2s_g * GEN ** K_LOG  # runtime m = K_LOG + tau_5, in the exponent
    zerocheck_r = HeapBuf(mr1cs_g ** 3)
    flock_pts = HeapBuf((mr1cs_g * GEN ** 2) ** FS_SLOTS)
    seed = flock_pts * (GEN ** (K_SKIP + N_FIXED_CHALLENGE_ROUNDS)) ** FS_SLOTS
    seed[0:4] = fs
    for xi in mul_range(GEN ** (K_SKIP + N_FIXED_CHALLENGE_ROUNDS), mr1cs_g):
        row = flock_pts * xi ** FS_SLOTS
        point_fs, zerocheck_challenge = squeeze(row[0:4])
        x3 = xi ** 3
        zerocheck_r[x3:x3 + 3] = zerocheck_challenge
        row[4:8] = point_fs
    pts_last = flock_pts * mr1cs_g ** FS_SLOTS
    fs = pts_last[0:4]
    # round-1 message (P = P^AB + P^C on Lambda, 2^K_SKIP scalars): fetch +
    # observe each as it comes off the stream, then sample z.
    zc_round1 = StackBuf(3 * 2 ** K_SKIP)
    for i in unroll(0, 2 ** K_SKIP):
        fs, w, cursor = fs_next(fs, cursor)
        k = 3 * i
        zc_round1[k:k + 3] = w
    fs, zerocheck_z = squeeze(fs)  # cursor now sits at the multilinear round messages, walked below
    # P(z), interpolated at z over ALL 128 phi8 nodes: the transmitted Lambda values
    # (nodes 64..128) plus the S half, zero by the zerocheck identity. The finished
    # sum is scaled once by the domain's inverse denominator; the full-domain
    # product only adds the S-half factor to the Lambda numerators.
    lagrange_nums = StackBuf(3 * 2 ** K_SKIP)
    lag64(zerocheck_z, lagrange_nums, 2 ** K_SKIP)
    s_half_product = ONE
    zc_running = ZERO  # the zerocheck running claim entering the multilinear rounds
    for i in unroll(0, 2 ** K_SKIP):
        k = 3 * i
        s_half_product = mul192(s_half_product, add192(zerocheck_z, phi8(i)))
        zc_running = add192(zc_running, mul192(lagrange_nums[k:k + 3], zc_round1[k:k + 3]))
    zc_running = mul192(zc_running, mul192(s_half_product, LAGRANGE_INV_COMBINED))
    for i in unroll(0, N_FIXED_CHALLENGE_ROUNDS):
        fs, g_1, cursor = fs_next(fs, cursor)  # G's coefficients, bar the constant one
        fs, g_2, cursor = fs_next(fs, cursor)
        g_0 = add192(zc_running, mul192(fixed_challenge(i), add192(g_1, g_2)))  # the eq-weighted split fixes it
        fs, chi_v = squeeze(fs)
        k = 3 * i
        zerocheck_chis[k:k + 3] = chi_v
        zc_running = add192(g_0, mul192(chi_v, add192(g_1, mul192(chi_v, g_2))))
    # the sampled rounds: K_LOG + tau_5 - K_SKIP in all, certified
    nmlv_g = tau_blake2s_g * GEN ** (K_LOG - K_SKIP)
    flock_rounds = HeapBuf((nmlv_g * GEN ** 2) ** ROUND_SLOTS)
    seed = flock_rounds * (GEN ** N_FIXED_CHALLENGE_ROUNDS) ** ROUND_SLOTS
    seed[0:4] = fs
    seed[GEN ** ROUND_CURSOR] = cursor
    seed[ROUND_CLAIM:ROUND_CLAIM + 3] = zc_running
    for xi in mul_range(GEN ** N_FIXED_CHALLENGE_ROUNDS, nmlv_g):
        rd = flock_rounds * xi ** ROUND_SLOTS
        x3 = xi ** 3
        r_at = x3 * GEN ** (3 * K_SKIP)
        round_fs, g_1, cur_i = fs_next(rd[0:4], rd[GEN ** ROUND_CURSOR])  # coefficients, bar the constant one
        round_fs, g_2, cur_i = fs_next(round_fs, cur_i)
        g_0 = add192(rd[ROUND_CLAIM:ROUND_CLAIM + 3], mul192(zerocheck_r[r_at:r_at + 3], add192(g_1, g_2)))  # the eq-weighted split fixes it
        round_fs, chi_v = squeeze(round_fs)
        zerocheck_chis[x3:x3 + 3] = chi_v
        nxt = rd * GEN ** ROUND_SLOTS
        nxt[0:4] = round_fs
        nxt[GEN ** ROUND_CURSOR] = cur_i
        nxt[ROUND_CLAIM:ROUND_CLAIM + 3] = add192(g_0, mul192(chi_v, add192(g_1, mul192(chi_v, g_2))))
    fr_last = flock_rounds * nmlv_g ** ROUND_SLOTS
    fs = fr_last[0:4]
    zc_running = fr_last[ROUND_CLAIM:ROUND_CLAIM + 3]
    cursor = fr_last[GEN ** ROUND_CURSOR]  # walked past all 2*n_mlv round scalars, now at a_eval
    # final: observe a_eval, b_eval; the terminal identity is what defines
    # c_eval, so nothing is checked here. C rode the rounds above, so all three
    # claims sit at the same point and lincheck pins all three at once.
    fs, a_eval, cursor = fs_next(fs, cursor)
    fs, b_eval, cursor = fs_next(fs, cursor)
    c_eval = add192(zc_running, mul192(a_eval, b_eval))
    # The phi8 Lagrange weights at z over the S nodes: the quirky extension's
    # own combination, which the lincheck terminal applies to the 64 slices.
    claim_nums = StackBuf(3 * 2 ** K_SKIP)
    lag64(zerocheck_z, claim_nums, 0)

    # ---- flock lincheck (matrix evaluation DEFERRED) ----
    matrix_eval = StackBuf(3)
    hint_witness(matrix_eval, "matpart")
    fs, lincheck_alpha = squeeze(fs)
    lincheck_beta = mul192(lincheck_alpha, lincheck_alpha)
    lincheck_cube = mul192(lincheck_beta, lincheck_alpha)
    # seed: a + alpha*b + alpha^2*c + alpha^3 (the two matrix claims, C, and the pin)
    lc_running = add192(add192(a_eval, mul192(lincheck_alpha, b_eval)), add192(mul192(lincheck_beta, c_eval), lincheck_cube))
    for i in unroll(0, LINCHECK_ROUNDS):
        fs, c0, cursor = fs_next(fs, cursor)  # q's coefficients, bar the linear one
        fs, c2, cursor = fs_next(fs, cursor)
        c1 = add192(lc_running, c2)  # the split fixes it against the running claim
        fs, rv = squeeze(fs)
        k = 3 * i
        lincheck_rs[k:k + 3] = rv
        lc_running = add192(c0, mul192(rv, add192(c1, mul192(rv, c2))))  # fold the degree-2 round poly at the challenge rv
    # post-sumcheck collapse: fetch + observe each scalar
    for i in unroll(0, 2 ** K_SKIP):
        fs, w, cursor = fs_next(fs, cursor)
        k = 3 * i
        z_partial[k:k + 3] = w
    # final consistency: running == matpart (DEFERRED) + beta * pin term. The
    # const-pin column folds through the top-variable bindings: weight =
    # prod_j (bit_{klog-1-j}(PIN_COLUMN) ? r_j : 1+r_j), surviving z_partial index
    # = PIN_COLUMN low 6 bits.
    pin = 3 * (PIN_COLUMN % 2 ** K_SKIP)
    pin_term = mul192(mul192(lincheck_cube, eq_weight(lincheck_rs, LINCHECK_ROUNDS, PIN_COLUMN, K_LOG)), z_partial[pin:pin + 3])
    # The C term. Its column weight is the row weight itself (C = I), and both
    # sides are tensors, so it collapses to eq(chi_in, chi_in_prime) times the
    # phi8 Lagrange combination of the 64 slices: no second matrix walk, no
    # second family.
    c_point_eq = ONE
    for t in unroll(0, LINCHECK_ROUNDS):
        zk = 3 * t
        lk = 3 * (LINCHECK_ROUNDS - 1 - t)
        c_point_eq = mul192(c_point_eq, add192(ONE, add192(zerocheck_chis[zk:zk + 3], lincheck_rs[lk:lk + 3])))
    c_slice_value = ZERO
    for i in unroll(0, 2 ** K_SKIP):
        k = 3 * i
        c_slice_value = add192(c_slice_value, mul192(claim_nums[k:k + 3], z_partial[k:k + 3]))
    c_slice_value = mul192(c_slice_value, LAGRANGE_INV_S)
    # deferred matrix eval + pin + C
    assert_eq192(lc_running, add192(add192(matrix_eval, pin_term), mul192(mul192(lincheck_beta, c_point_eq), c_slice_value)))
    # z_partial IS the claim: the terminal identity above pins its 64 slices, and
    # ring switching binds every one of them.
    return fs, cursor, zerocheck_z, lincheck_alpha, matrix_eval


def certify_placement(kappa_base, g_squares):
    # Certify the native order: descending kappa, then ascending column index.
    # Accumulate g^offset, with each column advancing it by g^(2^kappa).
    col_kappa_g = HeapBuf(N_COMMITTED_COLS)
    for c in unroll(0, N_COMMITTED_COLS):
        col_kappa_g[GEN ** c] = kappa_base[GEN ** COL_KAPPA_SRC[c]] * GEN ** COL_KAPPA_ADJ[c]
    col_sort_order = HeapBuf(N_COMMITTED_COLS)
    hint_witness(col_sort_order[0:N_COMMITTED_COLS], "col_sort_order")
    col_off_g = HeapBuf(N_COMMITTED_COLS)
    g_total = GEN ** 0
    prev_col = GEN ** 0
    prev_kappa = GEN ** 0
    for rank in unroll(0, N_COMMITTED_COLS):
        col = col_sort_order[GEN ** rank]
        assert log(col) < N_COMMITTED_COLS
        kappa_g = col_kappa_g[col]
        if rank != 0:
            # A negative exponent wraps around the order of GEN and cannot pass this
            # small range check, hence prev_kappa >= kappa.
            assert log(prev_kappa / kappa_g) < SIZE_BITS
            if prev_kappa == kappa_g:
                # Equal-sized columns use their compact (native column-order) index
                # as the deterministic ascending tie-break.
                assert log(col / prev_col) < N_COMMITTED_COLS
        col_off_g[col] = g_total  # write-once: a duplicate permutation entry collides
        # g_squares spans SIZE_BITS, and every kappa is under it: a certified log
        # <= 32 (log_mem or a tau), the baked bytecode log, or q_flock's tau_5 + 8.
        # Bound it before the lookup, independently of m derived from this product.
        assert log(kappa_g) < SIZE_BITS
        g_total *= g_squares[kappa_g]
        prev_col = col
        prev_kappa = kappa_g

    return g_total, col_off_g, col_kappa_g


def column_selector(offset, point, kappa: Const):
    # Rebuild the offset using only bits above the column's kappa, certifying its
    # alignment. The same bits select the column at the complete opening point.
    # Both offset and point are zero above m, so extending to MAX_STACK_LOG adds
    # only factors eq(0, 0) = 1.
    bits = StackBuf(MAX_STACK_LOG)
    hint_decompose_bits_exponent(bits, offset, MAX_STACK_LOG)
    rebuilt = GEN ** 0
    selector = ONE
    for k in unroll(kappa, MAX_STACK_LOG):
        bit = bits[k]
        bits[k] = bit * bit
        rebuilt *= 1 + bit * (1 + GEN ** (2 ** k))
        c = 3 * k
        selector = mul192(selector, add64(point[c:c + 3], 1 + bit))
    assert rebuilt == offset
    return selector


def check_opening_terminal(zeta, chi, r0: StackBuf(3), r1: StackBuf(3), g_bus_mu, g_zc_n, g_log_mem, tau_blake2s_g, claim_cplen_g, lam_pool, col_offsets, col_kappas, z_vals, c_table, point, inner_total: StackBuf(3), yr_at_tail: StackBuf(3), sumcheck_target: StackBuf(3)):
    # Evaluate each transparent weight at the complete point in witness order.
    # A claim is its low point followed by the certified column's selector bits;
    # q_flock slots prepend their fixed slot bits to the low point.
    zeta_eq_chain = HeapBuf(3 * (SIZE_BITS + 1))
    eq_prefix_chain(zeta_eq_chain, ONE, zeta, point, g_bus_mu)
    chi_eq_chain = HeapBuf(3 * (SIZE_BITS + 1))
    eq_prefix_chain(chi_eq_chain, ONE, chi, point, g_zc_n)
    chi_slot_eq_chain = HeapBuf(3 * (SIZE_BITS + 1))
    eq_prefix_chain(chi_slot_eq_chain, ONE, chi, point * GEN ** (3 * SLOT_STRIDE_LOG), tau_blake2s_g)
    # The PI claim's point is (r0, r1, 0, ..., 0) over log_mem coordinates.
    pi_chain = HeapBuf(3 * (SIZE_BITS + 1))
    pi_chain[3:6] = add192(ONE, add192(r0, point[0:3]))
    pi_chain[6:9] = mul192(pi_chain[3:6], add192(ONE, add192(r1, point[3:6])))
    for xk in mul_range(GEN ** 2, g_log_mem):
        x3 = xk ** 3
        nxt = x3 * GEN ** 3
        pi_chain[nxt:nxt + 3] = mul192(pi_chain[x3:x3 + 3], add192(ONE, point[x3:x3 + 3]))
    pi_end = g_log_mem ** 3
    pi_eq = pi_chain[pi_end:pi_end + 3]

    selectors = StackBuf(3 * N_COMMITTED_COLS)
    for c in unroll(0, N_COMMITTED_COLS):
        offset = col_offsets[GEN ** c]
        kappa_g = col_kappas[GEN ** c]
        selector = match(log(kappa_g), range(0, N_COLUMN_LOGS), lambda kappa: column_selector(offset, point, kappa))
        k = 3 * c
        selectors[k:k + 3] = selector

    inner_sum = inner_total
    for j in unroll(0, N_CLAIMS):
        if CLAIM_POINT_BUF[j] == POINT_BUF_PI:
            cplen_g = g_log_mem
            low_eq = pi_eq
        else:
            cplen_g = claim_cplen_g[GEN ** j]
        nlow = cplen_g
        low_at = cplen_g ** 3
        if CLAIM_POINT_BUF[j] == POINT_BUF_ZETA:
            low_eq = zeta_eq_chain[low_at:low_at + 3]
        if CLAIM_POINT_BUF[j] == POINT_BUF_RHO:
            low_eq = chi_eq_chain[low_at:low_at + 3]
        if CLAIM_POINT_BUF[j] == POINT_BUF_QFLOCK_RHO:
            slot_eq = ONE
            for k in unroll(0, SLOT_STRIDE_LOG):
                pk = 3 * k
                if CLAIM_QFLOCK_SLOT_BITS[SLOT_STRIDE_LOG * j + k] == 1:
                    slot_eq = mul192(slot_eq, point[pk:pk + 3])
                else:
                    slot_eq = mul192(slot_eq, add192(ONE, point[pk:pk + 3]))
            low_eq = mul192(slot_eq, chi_slot_eq_chain[low_at:low_at + 3])
            nlow = cplen_g * GEN ** SLOT_STRIDE_LOG
        assert nlow == col_kappas[GEN ** CLAIM_COMMITTED_COL[j]]
        lk = 3 * j
        sk = 3 * CLAIM_COMMITTED_COL[j]
        inner_sum = add192(inner_sum, mul192(mul192(lam_pool[lk:lk + 3], low_eq), selectors[sk:sk + 3]))

    qflockv_g = tau_blake2s_g * GEN ** SLOT_STRIDE_LOG
    assert qflockv_g == col_kappas[GEN ** QFLOCK_COMMITTED_COL]
    prod_chains = HeapBuf((qflockv_g * GEN) ** (3 * BASE_FIELD_BITS))
    for k in unroll(0, BASE_FIELD_BITS):
        c = 3 * k
        prod_chains[c:c + 3] = ONE
    rs_eq_run(prod_chains, z_vals, point, qflockv_g)
    prod_final = prod_chains * qflockv_g ** (3 * BASE_FIELD_BITS)
    rs_weight = ZERO
    for k in unroll(0, BASE_FIELD_BITS):
        c = 3 * k
        rs_weight = add192(rs_weight, mul192(c_table[c:c + 3], prod_final[c:c + 3]))
    qk = 3 * QFLOCK_COMMITTED_COL
    inner_sum = add192(inner_sum, mul192(rs_weight, selectors[qk:qk + 3]))
    assert_eq192(mul192(inner_sum, yr_at_tail), sumcheck_target)
    return


def verify_sub(pi: StackBuf(4), seed, g_logs_pow2, g_squares, defer_out):
    # In-circuit verification of ONE inner proof for the statement `pi`, mirroring
    # cpu::verify step for step; the `# ---- ... ----` headers below run in that
    # order. All proof data is hinted HERE, so each call pops the next sub-proof's
    # entry of every witness stream and the body lowers once. The exponent tables
    # are shared read-only; the deferred claims go to `defer_out`, three words an
    # element.
    #
    # The pool holds every committed-coordinate claim's value in decompose order
    # (the points are the GKR zetas, resolvable from the baked block structure) and
    # its certified low dimension, which the terminal pins its lengths against.
    claim_pool = HeapBuf(3 * N_CLAIMS)
    claim_cplen_g = HeapBuf(N_CLAIMS)

    # ---- seed (statement pre-bound: hinted sub pi + baked program digest) ----
    fs = StackBuf(4)
    blake2s(seed[0:4], pi, fs)
    stream = HeapBuf(STREAM_CAP)
    hint_witness(stream[0:STREAM_CAP], "stream")
    cursor = stream  # the proof stream, replayed scalar by scalar (advance = * g^3)

    # ---- announced layout and PCS rate (observed, then certified) ----
    # The stream announces the sizes as integer scalars, one log each, whose upper
    # limbs must be zero; the shape-generic phases need them as G-POWERS (loop
    # bounds, match scrutinees), so each is reassembled from its advice-decomposed
    # bits, with no hint and no g^j -> j lookup. Every table's rows are real rows
    # (the prover's fill blocks bring each count up to a power of two), so a height
    # is all there is to announce.
    sizes = StackBuf(N_TABLES + 2)
    for i in unroll(0, N_TABLES + 2):
        fs, x, cursor = fs_next(fs, cursor)
        assert x[1] == 0
        assert x[2] == 0
        sizes[i] = x[0]
    rate_sel = g_power_of_word(sizes[N_TABLES + 1], g_squares, LOG_WORD_BITS) / GEN
    assert log(rate_sel) < LIG_N_RATES
    dims_g = HeapBuf(N_TABLES + 1)  # [g^log_mem, g^tau_0 .. g^tau_{N_TABLES-1}]
    g_log_mem = g_power_of_word(sizes[0], g_squares, LOG_WORD_BITS)
    assert log(g_log_mem) < COUNT_BITS
    assert log(g_log_mem / GEN ** MIN_LOG_MEM) < COUNT_BITS  # native MIN_LOG_MEM <= log_mem
    dims_g[GEN ** 0] = g_log_mem
    for t in unroll(0, N_TABLES):
        g_tau = g_power_of_word(sizes[t + 1], g_squares, LOG_WORD_BITS)
        assert log(g_tau) < COUNT_BITS
        # A table's floor: flock sizes its BLAKE2s argument to at least 2^3 instances.
        assert log(g_tau / GEN ** FLOORS[t]) < COUNT_BITS
        dims_g[GEN ** (t + 1)] = g_tau
    # kappa_base maps a kappa source index to its certified announced log (source 0
    # = const via the baked adj). Each block's kappa then DERIVES from its
    # structural source as a compile-time offset off a certified log: no hint, and
    # nothing left free.
    kappa_base = HeapBuf(N_TABLES + 2)
    kappa_base[GEN ** 0] = 1
    kappa_base[GEN ** 1] = g_log_mem
    for t in unroll(0, N_TABLES):
        kappa_base[GEN ** (2 + t)] = dims_g[GEN ** (t + 1)]
    block_kappa = HeapBuf(N_BLOCKS)
    for b in unroll(0, N_BLOCKS):
        block_kappa[GEN ** b] = kappa_base[GEN ** BLOCK_KAPPA_SRC[b]] * GEN ** BLOCK_KAPPA_ADJ[b]
    # The ONE bus depth, COMPUTED (not hinted): mu = log2_ceil(Σ_b 2^κ_b) over
    # PUSH's blocks; pull matches by pairing, the count tree is padded to it.
    push_total = GEN ** 0
    for b in unroll(SIDE_BLOCK_START[PUSH_SIDE], SIDE_BLOCK_START[PUSH_SIDE + 1]):
        push_total *= g_squares[block_kappa[GEN ** b]]  # g^(sum of 2^kappa)
    g_bus_mu = log2_ceil_in_the_exponent(push_total, g_logs_pow2, g_squares, 0, SIZE_BITS)
    zeta = HeapBuf(g_bus_mu ** 3)  # the ONE shared GKR point: exactly mu coords

    # ---- commitment root (two halves), kept for the opening phase ----
    # A non-canonical half is rejected here (merkle.rs `scalars_to_hash`); the level
    # roots get the same treatment at their own read.
    fs, root_a, cursor = fs_next_half(fs, cursor)
    fs, root_b, cursor = fs_next_half(fs, cursor)
    commit_root = [root_a[0], root_a[1], root_b[0], root_b[1]]

    # ---- bus challenges (F192 provides the soundness margin without grinding) ----
    # A tuple is fingerprinted multilinearly: slot x weighs eq(alphas, x), so a leaf
    # factor has total degree N_TUPLE_BITS in the challenges and the aligned bytecode
    # polynomial is read off at the challenge vector itself (doc sec:gp, sec:e2e-bc).
    bus_alpha = HeapBuf(3 * N_TUPLE_BITS)
    for t in unroll(0, N_TUPLE_BITS):
        fs, av = squeeze(fs)
        k = 3 * t
        bus_alpha[k:k + 3] = av
    fp_w = HeapBuf(3 * N_TUPLE_SLOTS)
    for x in unroll(0, N_TUPLE_SLOTS):
        k = 3 * x
        fp_w[k:k + 3] = eq_weight(bus_alpha, N_TUPLE_BITS, x, 0)
    fs, beta = squeeze(fs)

    # ---- ONE GKR grand product: push, pull, and count RLC-batched ----
    fs, cursor, claim_push, claim_pull, claim_count = verify_bus_gkr(fs, cursor, g_bus_mu, zeta)

    # ---- the bus leaves, the table sumcheck, and the public-input claim ----
    chi = HeapBuf(3 * SIZE_BITS)  # chi[i] = the challenge that bound variable i
    fs, cursor, g_zc_n, bc_share, r0, r1 = verify_tables(fs, cursor, pi, zeta, g_bus_mu, dims_g, block_kappa, g_squares, fp_w, beta, claim_pool, claim_cplen_g, chi, claim_push, claim_pull, claim_count)

    # ---- flock zerocheck and lincheck (the matrix evaluation is DEFERRED) ----
    tau_blake2s_g = dims_g[GEN ** (TABLE_BLAKE2s + 1)]  # the BLAKE2s table's certified tau
    zerocheck_chis = HeapBuf((tau_blake2s_g * GEN ** (K_LOG - K_SKIP)) ** 3)  # m - 6 rounds
    lincheck_rs = HeapBuf(3 * LINCHECK_ROUNDS)
    z_partial = HeapBuf(3 * 2 ** K_SKIP)
    fs, cursor, zerocheck_z, lincheck_alpha, matrix_eval = verify_flock(fs, cursor, tau_blake2s_g, zerocheck_chis, lincheck_rs, z_partial)

    # ---- stacked mixed opening: ring-switch front + claim combination ----
    # The ring-switch slices are z_partial, read and bound above; this block only
    # binds them to the commitment. Compose six two-term F2-linear maps with shifts
    # 32,16,8,4,2,1: their expansion has all 64 Frobenius terms soundness needs,
    # while direct application costs 63 squarings and only six general
    # multiplications.
    map_challenges = HeapBuf(3 * 6)  # len(RING_MAP_SHIFTS)
    c_table = HeapBuf(3 * BASE_FIELD_BITS)
    z_vals = HeapBuf(3 * QFLOCK_VARS_CAP)
    for stage in unroll(0, len(RING_MAP_SHIFTS)):
        fs, map_challenge = squeeze(fs)
        k = 3 * stage
        map_challenges[k:k + 3] = map_challenge
    # Expand the same composition once for the later transparent-weight evaluation.
    # Before shift d, the populated coefficients are exactly at multiples of 2d; the
    # new branch fills the adjacent d-offset entries.
    c_table[0:3] = ONE
    for stage in unroll(0, len(RING_MAP_SHIFTS)):
        shift = RING_MAP_SHIFTS[stage]
        mk = 3 * stage
        map_challenge = map_challenges[mk:mk + 3]
        for slot in unroll(0, BASE_FIELD_BITS // (2 * shift)):
            src = 3 * (slot * 2 * shift)
            coefficient = c_table[src:src + 3]
            for k in unroll(0, shift):
                coefficient = mul192(coefficient, coefficient)
            dst = 3 * (slot * 2 * shift + shift)
            c_table[dst:dst + 3] = mul192(map_challenge, coefficient)
    # Evaluate the claim and combine its 64 packing rows: the running x-power (a
    # word) and the running sum ride one four-slot chain.
    rs_chain = HeapBuf(4 * ((2 ** K_SKIP) + 1))
    rs_chain[GEN ** 0] = GEN ** 0  # x^i
    rs_chain[1:4] = ZERO           # the running sum
    for x_round in mul_range(1, GEN ** (2 ** K_SKIP)):
        x3 = x_round ** 3
        lin_eval = z_partial[x3:x3 + 3]
        for stage in unroll(0, len(RING_MAP_SHIFTS)):
            frobenius = lin_eval
            for k in unroll(0, RING_MAP_SHIFTS[stage]):
                frobenius = mul192(frobenius, frobenius)
            mk = 3 * stage
            lin_eval = add192(lin_eval, mul192(map_challenges[mk:mk + 3], frobenius))
        row = rs_chain * x_round ** 4
        x_pow = row[GEN ** 0]
        row[GEN ** 4] = x_pow * 2
        row[5:8] = add192(row[1:4], scale(x_pow, lin_eval))
    rs_end = rs_chain * (GEN ** (2 ** K_SKIP)) ** 4
    transposed_claim = rs_end[1:4]
    # Suffix point for the transparent weight.
    for t in unroll(0, LINCHECK_ROUNDS):
        dst = 3 * t
        src = 3 * (LINCHECK_ROUNDS - 1 - t)
        z_vals[dst:dst + 3] = lincheck_rs[src:src + 3]
    zv_lo = z_vals * GEN ** (3 * LINCHECK_ROUNDS)
    zr_hi = zerocheck_chis * GEN ** (3 * LINCHECK_ROUNDS)
    for xt in mul_range(1, tau_blake2s_g):
        x3 = xt ** 3
        zv_lo[x3:x3 + 3] = zr_hi[x3:x3 + 3]
    # ONE batching challenge for the whole pool: N_CLAIMS - 1 fewer Fiat-Shamir
    # compressions than a challenge per claim, and none for the values themselves,
    # `fs_next` having bound every one of them as it read it, so `lam_cl` already
    # depends on all of them. Disjoint power ranges, as for the zc_xi-powers above:
    # the ring-switch claim takes lam_cl^0, the pool lam_cl^1 onward.
    fs, lam_cl = squeeze(fs)
    target = transposed_claim
    lam_pool = HeapBuf(3 * N_CLAIMS)
    lam_pow = lam_cl
    for j in unroll(0, N_CLAIMS):
        k = 3 * j
        lam_pool[k:k + 3] = lam_pow
        target = add192(target, mul192(lam_pow, claim_pool[k:k + 3]))
        lam_pow = mul192(lam_pow, lam_cl)

    g_total, col_offsets, col_kappas = certify_placement(kappa_base, g_squares)

    # ---- certify g^m: m = max(log2_ceil(sum_cols 2^kappa), PCS_MIN_MU) ----
    # g_total is g^(sum 2^kappa) from the certified placement walk above.
    gmv = log2_ceil_in_the_exponent(g_total, g_logs_pow2, g_squares, PCS_MIN_MU, SIZE_BITS)  # g^m
    size_sel = gmv * LIG_MIN_SHIFT_INV  # g^(m - MIN)
    assert log(size_sel) < LIG_N_LOG_SIZES
    # Flatten (rate-1, m-MIN) in rate-major order. Both coordinates are
    # transcript-bound and range-checked above, so a single compiled guest can
    # dispatch independently for every inner proof in a mixed-rate batch.
    config_sel = size_sel * rate_sel ** LIG_N_LOG_SIZES
    assert log(config_sel) < LIG_N_CANDIDATES
    sumcheck_target, point, inner_total, yr_at_tail = match(log(config_sel), range(0, LIG_N_CANDIDATES), lambda m_idx: open_stacked(m_idx, fs, target, commit_root, cursor))
    # `stream` is a fixed-capacity witness transport. The shape fixes the exact
    # consumed prefix, whose every word is transcript-bound; the unused suffix
    # is outside the recursively verified proof and intentionally unconstrained.

    # ---- generalized eval_b terminal (runtime claim shapes) ----
    check_opening_terminal(zeta, chi, r0, r1, g_bus_mu, g_zc_n, g_log_mem, tau_blake2s_g, claim_cplen_g, lam_pool, col_offsets, col_kappas, z_vals, c_table, point, inner_total, yr_at_tail, sumcheck_target)

    # ---- export this sub-proof's deferred-claim data to the caller (FRESH_*) ----
    for k in unroll(0, BYTECODE_LOG):
        c = 3 * k
        defer_out[c:c + 3] = zeta[c:c + 3]
    for k in unroll(0, LOG2_BYTECODE_COLS):
        src = 3 * k
        dst = 3 * (BYTECODE_LOG + k)
        defer_out[dst:dst + 3] = bus_alpha[src:src + 3]
    k = 3 * FRESH_BC_VALUE
    defer_out[k:k + 3] = bc_share
    k = 3 * FRESH_ALPHA
    defer_out[k:k + 3] = lincheck_alpha
    k = 3 * FRESH_Z_SKIP
    defer_out[k:k + 3] = zerocheck_z
    for k in unroll(0, LINCHECK_ROUNDS):
        c = 3 * k
        dst = 3 * (FRESH_ZCHI + k)
        defer_out[dst:dst + 3] = zerocheck_chis[c:c + 3]
        dst = 3 * (FRESH_LINCHECK_RS + k)
        defer_out[dst:dst + 3] = lincheck_rs[c:c + 3]
    for k in unroll(0, 2 ** K_SKIP):
        c = 3 * k
        dst = 3 * (FRESH_Z_PARTIAL + k)
        defer_out[dst:dst + 3] = z_partial[c:c + 3]
    k = 3 * FRESH_MATPART
    defer_out[k:k + 3] = matrix_eval
    return


# ============================ XMSS signature verification ===========================
# One signature of its epoch group's (epoch, message), against the signer's public
# key at `pk[0:4]` = (merkle_root, public_param), two words each. A tweak is two
# words: a constant first word, and the index word shared by every hash at one
# epoch or, for a Merkle node, the parent's. Index table layout (at cell g^t):
#     0              : the epoch's index word (encoding, chains, wots-pk)
#     1 + l          : the parent index word of Merkle level l < LOG_LIFETIME


def fill_xmss_epoch_tables(epoch, merkle_bits, index_table):
    # The index words and the Merkle direction bits at `epoch`, shared by every XMSS
    # signature this node verifies at it. One bit decomposition gives all three uses:
    # a tweak's index field is the epoch (encoding, chain, wots-pk) or the parent
    # index `epoch >> (l + 1)` at Merkle level l, and the direction bit at that
    # level IS bit l. Booleanity is a write-once pin and the reconstruction ties the
    # bits back to the epoch, which also bounds it to LOG_LIFETIME bits. SPHINCS
    # shares none of this, deriving every tweak from the index its own digest picks,
    # which is neither public nor shared between signers.
    hint_decompose_bits(merkle_bits, epoch, LOG_LIFETIME)
    bits = StackBuf(LOG_LIFETIME)
    reconstructed = 0
    index = 0
    for b in unroll(0, LOG_LIFETIME):
        bit = merkle_bits[GEN ** b]
        merkle_bits[GEN ** b] = bit * bit
        bits[b] = bit
        reconstructed += bit * 2 ** b
        index += bit * XM_INDEX_WEIGHT[b]
    assert reconstructed == epoch
    index_table[GEN ** 0] = index
    # Merkle level lvl - 1 hashes the parent at `epoch >> lvl`: the epoch's bits from
    # lvl up, each weighed lvl places down. The top level gets the empty sum.
    for lvl in unroll(1, LOG_LIFETIME + 1):
        parent = 0
        for b in unroll(lvl, LOG_LIFETIME):
            parent += bits[b] * XM_INDEX_WEIGHT[b - lvl]
        index_table[GEN ** lvl] = parent
    return


def verify_sig(message, index_table, merkle_bits, pk):
    pp = pk[2:4]
    index = index_table[GEN ** 0]

    # Encoding digest D = BLAKE2s(tweak | pp | msg | randomness | zero-pad), 96
    # bytes: one full 64-byte block then a 32-byte final block, 24 bytes of
    # randomness and the specified 8-byte zero pad, which is a zero word.
    after_msg = StackBuf(4)
    blake2s([XM_ENC_TWEAK, index, pp], message[0:4], after_msg, counter=64, final=0)
    rand = StackBuf(3)
    hint_witness(rand, "rand")
    digest = StackBuf(4)
    blake2s([rand, 0], [0, 0, 0, 0], digest, cv=after_msg, counter=96, final=1)

    # V WOTS chains. Per chain the digit is hinted in the exponent (g^{e_i}), range
    # checked and dispatched once; arm k walks the remaining CHAIN_STEPS-k steps and
    # returns the tip plus the digit literal. The product of the digits is the
    # target sum (g^{Σe_i}); the digits, weighted by CHAIN_LENGTH^i inside their own
    # digest word (DIGITS_PER_WORD digits a word, GF(2^64)'s monomial budget, each
    # word's leftover top bits ground to zero by the signer), reconstruct D's first
    # two words.
    tips = StackBuf(TIP_WORDS)
    digit_product = 1
    acc_lo = 0
    acc_hi = 0
    for i in unroll(0, V):
        digit = hint_witness("digits")
        assert log(digit) < CHAIN_LENGTH
        start = StackBuf(2)
        hint_witness(start, "chain_starts")
        tips[2 * i], tips[2 * i + 1], e = match(log(digit), range(0, CHAIN_LENGTH), lambda k: walk(start[0], start[1], XM_CHAIN_TWEAK + i * CHAIN_LENGTH * XM_P_MUL, index, pp[0], pp[1], k))
        digit_product = digit_product * digit
        term = e * CHAIN_LENGTH ** (i % DIGITS_PER_WORD)  # e_i in its monomial subspace
        if i // DIGITS_PER_WORD == 0:
            acc_lo = acc_lo + term
        else:
            acc_hi = acc_hi + term
    assert digit_product == GEN ** TARGET_SUM
    assert acc_lo == digest[0]
    assert acc_hi == digest[1]

    # WOTS public-key leaf = standard BLAKE2s over prefix + V tips: WOTS_PK_BLOCKS
    # full blocks, carrying the chaining value between instructions.
    leaf = StackBuf(4)
    blake2s([XM_PK_TWEAK, index, pp], tips[0:4], leaf, counter=64, final=0)
    for q in unroll(1, WOTS_PK_BLOCKS):
        next_leaf = StackBuf(4)
        blake2s(tips[8 * q - 4:8 * q], tips[8 * q:8 * q + 4], next_leaf, cv=leaf, counter=64 * (q + 1), final=(q + 1) // WOTS_PK_BLOCKS)
        leaf = next_leaf

    # Merkle path from the leaf to the root: the epoch bit orders the two children at
    # each level, and the tweak carries that level's parent index.
    n0 = leaf[0]
    n1 = leaf[1]
    for lvl in unroll(0, LOG_LIFETIME):
        sibling = StackBuf(2)
        hint_witness(sibling, "siblings")
        children = order_children(n0, n1, sibling, merkle_bits[GEN ** lvl])
        parent = StackBuf(4)
        blake2s([XM_MERKLE_TWEAK + const((lvl + 1) * XM_P_MUL), index_table[GEN ** (lvl + 1)], pp], children, parent)
        n0 = parent[0]
        n1 = parent[1]
    assert n0 == pk[1]
    assert n1 == pk[GEN]
    return


def walk(v0, v1, tw, index, pp0, pp1, k: Const):
    # Walk WOTS chain steps k..CHAIN_STEPS-1: value' = H(tweak|pp, value|0). Step s's
    # tweak is the chain's first word plus s sub-positions.
    w0 = v0
    w1 = v1
    for s in unroll(k, CHAIN_STEPS):
        out = StackBuf(4)
        blake2s([tw + s * XM_P_MUL, index, pp0, pp1], [w0, w1, 0, 0], out, counter=48, final=1)
        w0 = out[0]
        w1 = out[1]
    return w0, w1, k


# ========================== SPHINCS+ signature verification =========================


@inline
def sp_bit_field(bits_ptr, off: Const, n: Const, pos: Const):
    # The integer held by bits [off, off+n) of the digest, weighed into a tweak word
    # at bit `pos`: a tweak field placed where the tweak wants it, one fused
    # multiply-add a bit, whatever digest word the bits came from.
    acc = 0
    for i in unroll(0, n):
        acc += bits_ptr[GEN ** (off + i)] * 2 ** (pos + i)
    return acc


def sp_walk(v0, v1, tw, tw1, pp0, pp1, k: Const):
    # Walk chain steps k..SP_CHAIN_STEPS-1: value' = Th(P, tw_chain, value).
    # `tw` already carries the type byte, the layer and 2^w*i, and `tw1` the
    # position (tau, e), so step s's tweak is one addition of a compile-time literal.
    w0 = v0
    w1 = v1
    for s in unroll(k, SP_CHAIN_STEPS):
        out = StackBuf(4)
        blake2s([tw + s * SP_P_MUL, tw1, pp0, pp1], [w0, w1, 0, 0], out, counter=48, final=1)
        w0 = out[0]
        w1 = out[1]
    return w0, w1, k


def sp_ots_leaf(tw_lay, tw1, pp0, pp1, m0, m1):
    # One layer's one-time verification: the encoding of `m` under the hinted
    # counter, the V chains walked from the revealed values, and the leaf they hash
    # to. `tw_lay` is the layer's first-word field and `tw1` the position word (tau,
    # e); this function is called once per layer, so the V dispatch tables are
    # compiled once for the whole scheme.
    ctr = hint_witness("sp_counter")
    ctr_bits = HeapBuf(GEN ** SP_COUNTER_BITS)
    hint_decompose_bits(ctr_bits, ctr, SP_COUNTER_BITS)
    bind_bits(ctr_bits, ctr, SP_COUNTER_BITS)  # LE_32: four counter bytes, four of padding

    # D = Th(P, tw_enc, m | LE_32(c)), a 52-byte one-block hash.
    digest = StackBuf(4)
    blake2s([tw_lay + SP_TW_ENC, tw1, pp0, pp1], [m0, m1, ctr, 0], digest, counter=52, final=1)

    # The codeword, as in XMSS: each digit hinted in the exponent, range checked and
    # dispatched once, arm k walking the remaining steps; the product of the digits
    # is the target sum, and the digits weighted by 2^w within each digest word
    # reconstruct D, which pins each word's leftover top bits to zero.
    tips = StackBuf(SP_TIP_WORDS)
    digit_product = 1
    acc_lo = 0
    acc_hi = 0
    for i in unroll(0, SP_V):
        digit = hint_witness("sp_digits")
        assert log(digit) < SP_CHAIN_LENGTH
        start = StackBuf(2)
        hint_witness(start, "sp_chain_starts")
        tips[2 * i], tips[2 * i + 1], e = match(log(digit), range(0, SP_CHAIN_LENGTH), lambda k: sp_walk(start[0], start[1], tw_lay + SP_TW_CHAIN + i * SP_CHAIN_MUL, tw1, pp0, pp1, k))
        digit_product = digit_product * digit
        term = e * SP_CHAIN_LENGTH ** (i % SP_DIGITS_PER_WORD)
        if i // SP_DIGITS_PER_WORD == 0:
            acc_lo = acc_lo + term
        else:
            acc_hi = acc_hi + term
    assert digit_product == GEN ** SP_TARGET_SUM
    assert acc_lo == digest[0]
    assert acc_hi == digest[1]

    leaf = StackBuf(4)
    blake2s([tw_lay + SP_TW_LEAF, tw1, pp0, pp1], tips[0:4], leaf, counter=64, final=0)
    for q in unroll(1, SP_LEAF_BLOCKS):
        next_leaf = StackBuf(4)
        blake2s(tips[8 * q - 4:8 * q], tips[8 * q:8 * q + 4], next_leaf, cv=leaf, counter=64 * (q + 1), final=(q + 1) // SP_LEAF_BLOCKS)
        leaf = next_leaf
    return leaf[0], leaf[1]


def verify_sig_sphincs(signer):
    # `signer` is one 8-word entry of the SPHINCS coverage table: the key's root and
    # public parameter, then the message THAT signer signed. Where XMSS's message is
    # one statement field for the whole node, a SPHINCS message rides its own slot,
    # and the signer-set digest binds the two together.
    pp = signer[2:4]

    # ---- the message digest, which chooses the few-time key ----
    # D = Truncate(H(tw_msg | P | rho | root | m)), 96 bytes in two blocks.
    rho = StackBuf(2)
    hint_witness(rho, "sp_rand")
    prefix = StackBuf(4)
    blake2s([SP_TW_MSG, 0, pp], [rho, signer[0:2]], prefix, counter=64, final=0)
    digest = StackBuf(4)
    blake2s(signer[4:8], [0, 0, 0, 0], digest, cv=prefix, counter=96, final=1)

    # The index and the k leaf indices are bit fields of that digest, so its bits are
    # advice-decomposed here and bound word by word. Nothing else derives them: every
    # tweak below is built from these bits.
    bits = HeapBuf(GEN ** SP_BIT_CELLS)
    for lane in unroll(0, SP_BIT_LANES):
        lane_bits = bits * GEN ** (lane * BASE_FIELD_BITS)
        hint_decompose_bits(lane_bits, digest[lane], BASE_FIELD_BITS)
        bind_bits(lane_bits, digest[lane], BASE_FIELD_BITS)

    # The digest is admissible only if its last leaf index is zero, which is what
    # lets the forest drop that tree.
    for b in unroll(0, SP_A):
        assert bits[GEN ** (SP_H + (SP_K - 1) * SP_A + b)] == 0

    # ---- the few-time signature: one opened leaf per tree of the forest ----
    idx_tau = sp_bit_field(bits, 0, SP_H, SP_TAU_POS)
    roots = StackBuf(2 * SP_N_FTS)
    for kappa in unroll(0, SP_N_FTS):
        leaf_off = SP_H + kappa * SP_A
        secret = StackBuf(2)
        hint_witness(secret, "sp_fts_secrets")
        fts_leaf = StackBuf(4)
        node_index = sp_bit_field(bits, leaf_off, SP_A, SP_J_POS)
        blake2s([SP_TW_FTS_LEAF + kappa * SP_LAY_MUL, idx_tau + node_index, pp], [secret, 0, 0], fts_leaf, counter=48, final=1)
        n0 = fts_leaf[0]
        n1 = fts_leaf[1]
        for level in unroll(0, SP_A):
            sibling = StackBuf(2)
            hint_witness(sibling, "sp_fts_paths")
            children = order_children(n0, n1, sibling, bits[GEN ** (leaf_off + level)])
            parent = StackBuf(4)
            if const(level + 1 == SP_A):
                node_index = 0
            else:
                # The index fits in one word; clearing its low bit makes division by GEN a right shift.
                node_index = (node_index + bits[GEN ** (leaf_off + level)] * 2 ** SP_J_POS) / GEN
            blake2s([SP_TW_FTS_NODE + kappa * SP_LAY_MUL + const((level + 1) * SP_P_MUL), idx_tau + node_index, pp], children, parent)
            n0 = parent[0]
            n1 = parent[1]
        roots[2 * kappa] = n0
        roots[2 * kappa + 1] = n1
    fts_key = StackBuf(4)
    blake2s([SP_TW_FTS_ROOTS, idx_tau, pp], roots[0:4], fts_key, counter=64, final=0)
    for q in unroll(1, SP_ROOT_BLOCKS):
        next_key = StackBuf(4)
        blake2s(roots[8 * q - 4:8 * q], roots[8 * q:8 * q + 4], next_key, cv=fts_key, counter=64 * (q + 1), final=(q + 1) // SP_ROOT_BLOCKS)
        fts_key = next_key
    s0 = fts_key[0]
    s1 = fts_key[1]

    # ---- the hypertree, bottom layer first ----
    # Layer lay signs what the layer below produced: the few-time key at the bottom,
    # that layer's root above it, and the public key's root at the top.
    for step in unroll(0, SP_D):
        lay = SP_D - 1 - step
        leaf_index_off = SP_SUFFIX[lay + 1]
        tau_field = sp_bit_field(bits, SP_SUFFIX[lay], SP_H - SP_SUFFIX[lay], SP_TAU_POS)
        node_index = sp_bit_field(bits, leaf_index_off, SP_HEIGHTS[lay], SP_J_POS)
        n0, n1 = sp_ots_leaf(lay * SP_LAY_MUL, tau_field + node_index, pp[0], pp[1], s0, s1)
        for level in unroll(0, SP_HEIGHTS[lay]):
            sibling = StackBuf(2)
            hint_witness(sibling, "sp_siblings")
            children = order_children(n0, n1, sibling, bits[GEN ** (leaf_index_off + level)])
            parent = StackBuf(4)
            if const(level + 1 == SP_HEIGHTS[lay]):
                node_index = 0
            else:
                node_index = (node_index + bits[GEN ** (leaf_index_off + level)] * 2 ** SP_J_POS) / GEN
            blake2s([SP_TW_NODE + lay * SP_LAY_MUL + const((level + 1) * SP_P_MUL), tau_field + node_index, pp], children, parent)
            n0 = parent[0]
            n1 = parent[1]
        s0 = n0
        s1 = n1
    assert s0 == signer[1]
    assert s1 == signer[GEN]
    return


# =========================== statements and the signer set ==========================


def statement_digest(seed, signers: StackBuf(4), da: StackBuf(4), defer):
    # A node's statement, hashed to the four words the VM publishes, over the
    # proving environment's Fiat-Shamir seed (at `seed`: flock's R1CS and this
    # bytecode), the signer-set digest, the digest of its possibly empty DA root
    # list, and the DEFER_STMT_CELLS deferred elements. A parent rebuilds a child's
    # statement with this same call, over a signer-set digest it re-absorbed itself,
    # which forces the child to be a proof of THIS bytecode over groups checked
    # against the parent's own.
    #
    # The preimage is fixed-length, so a plain BLAKE2s beats the Fiat-Shamir chain:
    # the seed and signer-set digest are the first block, then the DA digest and
    # the deferred elements' limbs, zero-filled to a whole block.
    words = StackBuf(8 * (STMT_BLOCKS - 1))
    words[0:4] = da
    for p in unroll(0, DEFER_STMT_CELLS):
        k = 3 * p
        words[4 + k:4 + k + 3] = defer[k:k + 3]
    for k in unroll(0, STMT_PAD):
        words[4 + 3 * DEFER_STMT_CELLS + k] = 0
    st = StackBuf(4)
    blake2s(seed[0:4], signers, st, counter=64, final=0)
    for b in unroll(1, STMT_BLOCKS):
        lo = 8 * (b - 1)
        nxt = StackBuf(4)
        blake2s(words[lo:lo + 4], words[lo + 4:lo + 8], nxt, cv=st, counter=64 * (b + 1), final=(b + 1) // STMT_BLOCKS)
        st = nxt
    return st


def keys_window(state: StackBuf(4), base, keys_ptr, x_q, g_squares):
    # One window of an epoch group's key hash: SIGNERS_WINDOW blocks, two declared
    # keys each (a key is four words, a block eight). Counters as in `sphincs_window`.
    nxt = scaled_log(x_q * GEN, g_squares, const(6 + SIGNERS_WINDOW_LOG))
    st = state
    for j in unroll(0, SIGNERS_WINDOW):
        pair = keys_ptr * GEN ** (8 * j)
        hint_witness(pair[0:8], "pubkeys")
        out = StackBuf(4)
        if const(j + 1 == SIGNERS_WINDOW):
            blake2s(pair[0:4], pair[4:8], out, cv=st, md=[nxt, 0])
        else:
            blake2s(pair[0:4], pair[4:8], out, cv=st, md=[base + const(64 * (j + 1)), 0])
        st = out
    return st, nxt




def list_chunk(state: StackBuf(4), off, ptr, cover, marks, origin_g, limit_g, size: Const, kind: Const):
    # `size` non-final blocks of a list hash, block j's counter `off + 64(j + 1)`,
    # its contents by list kind (`tail_blocks`).
    st = state
    for j in unroll(0, size):
        out = StackBuf(4)
        md = [off + const(64 * (j + 1)), 0]
        if const(kind == LIST_CHILD_KEYS):
            two = StackBuf(2)
            hint_witness(two, "child_index")
            assert log(two[0]) < log(limit_g)
            assert log(two[1]) < log(limit_g)
            cover[origin_g * two[0]] = marks * GEN ** (2 * j)
            cover[origin_g * two[1]] = marks * GEN ** (2 * j + 1)
            key_a = ptr * two[0] ** 4
            key_b = ptr * two[1] ** 4
            blake2s(key_a[0:4], key_b[0:4], out, cv=st, md=md)
        if const(kind == LIST_CHILD_SPHINCS):
            off_hint = hint_witness("child_sphincs_index")
            assert log(off_hint) < log(limit_g)
            cover[origin_g * off_hint] = marks * GEN ** j
            entry = ptr * off_hint ** 8
            blake2s(entry[0:4], entry[4:8], out, cv=st, md=md)
        if const(kind // 3 == 0):
            block = ptr * GEN ** (8 * j)
            if const(kind == LIST_KEYS):
                hint_witness(block[0:8], "pubkeys")
            if const(kind == LIST_SPHINCS):
                hint_witness(block[0:8], "sphincs_signers")
            blake2s(block[0:4], block[4:8], out, cv=st, md=md)
        st = out
    return st


def tail_blocks(state: StackBuf(4), base, ptr, cover, marks, origin_g, limit_g, tail_g, kind: Const):
    # The blocks a list hash has left past its last whole window, fewer than a
    # window: tail_g = g^k, absorbed in power-of-two chunks, largest first, one per
    # set bit of k. A chunk starts at a multiple of twice its size, so every counter
    # offset 64(start + j + 1) in it is still one XOR onto the running base, and one
    # chunk per size serves every k. Returns the state, then the list pointer and the
    # coverage marks stepped past the tail.
    bits = StackBuf(SIGNERS_WINDOW_LOG)
    hint_decompose_bits_exponent(bits, tail_g, SIGNERS_WINDOW_LOG)
    states = StackBuf(4 * (SIGNERS_WINDOW_LOG + 1))
    states[0:4] = state
    rebuilt = GEN ** 0
    off = base
    for i in unroll(0, SIGNERS_WINDOW_LOG):
        b = SIGNERS_WINDOW_LOG - 1 - i
        bit = bits[b]
        bits[b] = bit * bit  # booleanity, as a write-once pin
        rebuilt *= 1 + bit * (GEN ** (2 ** b) + 1)
        cur = 4 * i
        if bit != 0:
            states[cur + 4:cur + 8] = list_chunk(states[cur:cur + 4], off, ptr, cover, marks, origin_g, limit_g, 2 ** b, kind)
        else:
            states[cur + 4:cur + 8] = states[cur:cur + 4]
        off = off + bit * const(64 * 2 ** b)
        if const(kind // 3 == 0):
            ptr = ptr * (1 + bit * (GEN ** (8 * 2 ** b) + 1))
        if const(kind == LIST_CHILD_KEYS):
            marks = marks * (1 + bit * (GEN ** (2 * 2 ** b) + 1))
        if const(kind == LIST_CHILD_SPHINCS):
            marks = marks * (1 + bit * (GEN ** (2 ** b) + 1))
    assert rebuilt == tail_g
    last = 4 * SIGNERS_WINDOW_LOG
    return states[last:last + 4], ptr, marks


def key_list_digest(keys_ptr, half_g, odd_g, n_keys_g, g_squares):
    # BLAKE2s of one epoch group's declared key list: 32 bytes a key, so the hashed
    # string is 32·n bytes and its last block is the only partial one. The n // 2
    # pairs and the odd key out make half + odd blocks; all but the last run in
    # windows plus a tail (doc §sec:prog-byte-counter), and the last carries the
    # total length as its counter and the final-block flag.
    split = StackBuf(2)
    hint_witness(split, "signers_split")  # g^windows, g^tail_blocks
    windows = split[0]
    tail = split[1]
    assert log(tail) < SIGNERS_WINDOW
    assert log(windows) < SIGNERS_MAX_WINDOWS
    assert windows ** SIGNERS_WINDOW * tail == half_g * odd_g * INV_GEN
    chain = HeapBuf((windows * GEN) ** 6)  # state, base, first key of the window
    chain[0:4] = [BLAKE2S_IV_0, BLAKE2S_IV_1, BLAKE2S_IV_2, BLAKE2S_IV_3]
    chain[GEN ** 4] = 0
    chain[GEN ** 5] = keys_ptr
    for xq in mul_range(1, windows):
        slot = chain * xq ** 6
        st, nb = keys_window(slot[0:4], slot[GEN ** 4], slot[GEN ** 5], xq, g_squares)
        step = slot * GEN ** 6
        step[0:4] = st
        step[GEN ** 4] = nb
        step[GEN ** 5] = slot[GEN ** 5] * GEN ** (8 * SIGNERS_WINDOW)
    end = chain * windows ** 6
    t, last, unused = tail_blocks(end[0:4], end[GEN ** 4], end[GEN ** 5], 0, 0, 0, 0, tail, LIST_KEYS)
    final = [scaled_log(n_keys_g, g_squares, 5), MD_FINAL]
    digest = StackBuf(4)
    if odd_g == 1:
        hint_witness(last[0:8], "pubkeys")
        blake2s(last[0:4], last[4:8], digest, cv=t, md=final)
    else:
        # The odd key out fills half its block, the rest being the zero bytes the
        # counter already accounts for.
        hint_witness(last[0:4], "pubkeys")
        blake2s(last[0:4], [0, 0, 0, 0], digest, cv=t, md=final)
    return digest


def child_keys_window(state: StackBuf(4), base, keys_ptr, cover, marks, origin_g, limit_g, x_q, g_squares):
    # One window of a child's key hash, absorbed exactly as the child absorbed it,
    # but with both keys of a block read at hinted indices into THIS node's table and
    # marked in the coverage table. Each index is an offset into the parent group the
    # caller mapped this child group to, bounded by that group's size, so a child's
    # key can only ever land on an XMSS slot of the right epoch.
    nxt = scaled_log(x_q * GEN, g_squares, const(6 + SIGNERS_WINDOW_LOG))
    st = state
    for j in unroll(0, SIGNERS_WINDOW):
        two = StackBuf(2)
        hint_witness(two, "child_index")
        assert log(two[0]) < log(limit_g)  # precondition as in the raw loops
        assert log(two[1]) < log(limit_g)
        cover[origin_g * two[0]] = marks * GEN ** (2 * j)
        cover[origin_g * two[1]] = marks * GEN ** (2 * j + 1)
        key_a = keys_ptr * two[0] ** 4
        key_b = keys_ptr * two[1] ** 4
        out = StackBuf(4)
        if const(j + 1 == SIGNERS_WINDOW):
            blake2s(key_a[0:4], key_b[0:4], out, cv=st, md=[nxt, 0])
        else:
            blake2s(key_a[0:4], key_b[0:4], out, cv=st, md=[base + const(64 * (j + 1)), 0])
        st = out
    return st, nxt




def child_key_list_digest(keys_ptr, cover, base, origin_g, limit_g, half_g, odd_g, n_keys_g, g_squares):
    # BLAKE2s of one epoch group of a child's keys, over the same 32·n bytes the
    # child hashed (`key_list_digest`), so the digest it rebuilds is the one the
    # child's statement carries. `base` prefixes the coverage write values, which
    # count the keys off as they are marked.
    split = StackBuf(2)
    hint_witness(split, "signers_split")
    windows = split[0]
    tail = split[1]
    assert log(tail) < SIGNERS_WINDOW
    assert log(windows) < SIGNERS_MAX_WINDOWS
    assert windows ** SIGNERS_WINDOW * tail == half_g * odd_g * INV_GEN
    chain = HeapBuf((windows * GEN) ** 6)  # state, base, coverage marks
    chain[0:4] = [BLAKE2S_IV_0, BLAKE2S_IV_1, BLAKE2S_IV_2, BLAKE2S_IV_3]
    chain[GEN ** 4] = 0
    chain[GEN ** 5] = base
    for xq in mul_range(1, windows):
        slot = chain * xq ** 6
        st, nb = child_keys_window(slot[0:4], slot[GEN ** 4], keys_ptr, cover, slot[GEN ** 5], origin_g, limit_g, xq, g_squares)
        step = slot * GEN ** 6
        step[0:4] = st
        step[GEN ** 4] = nb
        step[GEN ** 5] = slot[GEN ** 5] * GEN ** (2 * SIGNERS_WINDOW)
    end = chain * windows ** 6
    t, unused, marks = tail_blocks(end[0:4], end[GEN ** 4], keys_ptr, cover, end[GEN ** 5], origin_g, limit_g, tail, LIST_CHILD_KEYS)
    final = [scaled_log(n_keys_g, g_squares, 5), MD_FINAL]
    digest = StackBuf(4)
    if odd_g == 1:
        two = StackBuf(2)
        hint_witness(two, "child_index")
        assert log(two[0]) < log(limit_g)
        assert log(two[1]) < log(limit_g)
        cover[origin_g * two[0]] = marks
        cover[origin_g * two[1]] = marks * GEN
        key_a = keys_ptr * two[0] ** 4
        key_b = keys_ptr * two[1] ** 4
        blake2s(key_a[0:4], key_b[0:4], digest, cv=t, md=final)
    else:
        tail_idx = hint_witness("child_index")
        assert log(tail_idx) < log(limit_g)
        cover[origin_g * tail_idx] = marks
        key_last = keys_ptr * tail_idx ** 4
        blake2s(key_last[0:4], [0, 0, 0, 0], digest, cv=t, md=final)
    return digest


def scaled_log(x, g_squares, shift: Const):
    # 2^shift times the exponent of `x`, as a bit pattern (doc §sec:prog-byte-counter).
    # The exponent's bits are advice, tied back by the g-power product; weighing them
    # at 2^j assembles the exponent itself and the final multiply is the shift,
    # exact because nothing reduces below degree 64. Both sides of the product stay
    # under the order of g, so the bits ARE that exponent, hence below
    # 2^SIGNERS_COUNT_BITS, which every count and window index here is.
    bits = StackBuf(SIGNERS_COUNT_BITS)
    hint_decompose_bits_exponent(bits, x, SIGNERS_COUNT_BITS)
    value = 0
    rebuilt = GEN ** 0
    for j in unroll(0, SIGNERS_COUNT_BITS):
        b = bits[j]
        bits[j] = b * b  # booleanity, as a write-once pin
        value += b * 2 ** j
        rebuilt *= (1 + b * (g_squares[GEN ** j] + 1))
    assert rebuilt == x
    return value * 2 ** shift


def sphincs_window(state: StackBuf(4), base, entries_ptr, x_q, g_squares):
    # One window of the SPHINCS list's hash: SIGNERS_WINDOW claims, one 64-byte block
    # each (the claimed key, then the message it signed). Block j's counter is
    # base + 64(j+1), one XOR, except the last, whose offset is the base's own lowest
    # bit and which therefore takes the NEXT window's base as its whole counter. That
    # base is derived here and carried out for the following window.
    nxt = scaled_log(x_q * GEN, g_squares, const(6 + SIGNERS_WINDOW_LOG))
    st = state
    for j in unroll(0, SIGNERS_WINDOW):
        entry = entries_ptr * GEN ** (8 * j)
        hint_witness(entry[0:8], "sphincs_signers")
        out = StackBuf(4)
        if const(j + 1 == SIGNERS_WINDOW):
            blake2s(entry[0:4], entry[4:8], out, cv=st, md=[nxt, 0])
        else:
            blake2s(entry[0:4], entry[4:8], out, cv=st, md=[base + const(64 * (j + 1)), 0])
        st = out
    return st, nxt




def sphincs_list_digest(entries_ptr, n_g, g_squares):
    # BLAKE2s of the declared SPHINCS claims: n blocks of 64 bytes, so the hash is
    # over exactly 64n bytes and no block is partial. The last block is absorbed
    # apart, carrying the total length as its counter and the final-block flag; the
    # n - 1 before it run in windows plus a tail (doc §sec:prog-byte-counter).
    digest = StackBuf(4)
    if n_g == 1:
        # No claims: the hash of the empty string, one compression of a zero block.
        blake2s([0, 0, 0, 0], [0, 0, 0, 0], digest, md=[0, MD_FINAL])
    else:
        split = StackBuf(2)
        hint_witness(split, "signers_split")  # g^windows, g^tail_blocks
        windows = split[0]
        tail = split[1]
        assert log(tail) < SIGNERS_WINDOW
        assert log(windows) < SIGNERS_MAX_WINDOWS
        assert windows ** SIGNERS_WINDOW * tail == n_g * INV_GEN
        # Six words a window: the state, the window's base, its first entry.
        chain = HeapBuf((windows * GEN) ** 6)
        chain[0:4] = [BLAKE2S_IV_0, BLAKE2S_IV_1, BLAKE2S_IV_2, BLAKE2S_IV_3]
        chain[GEN ** 4] = 0
        chain[GEN ** 5] = entries_ptr
        for xq in mul_range(1, windows):
            slot = chain * xq ** 6
            st, nb = sphincs_window(slot[0:4], slot[GEN ** 4], slot[GEN ** 5], xq, g_squares)
            step = slot * GEN ** 6
            step[0:4] = st
            step[GEN ** 4] = nb
            step[GEN ** 5] = slot[GEN ** 5] * GEN ** (8 * SIGNERS_WINDOW)
        end = chain * windows ** 6
        t, last, unused = tail_blocks(end[0:4], end[GEN ** 4], end[GEN ** 5], 0, 0, 0, 0, tail, LIST_SPHINCS)
        hint_witness(last[0:8], "sphincs_signers")
        final = [scaled_log(n_g, g_squares, 6), MD_FINAL]
        blake2s(last[0:4], last[4:8], digest, cv=t, md=final)
    return digest


def child_sphincs_window(state: StackBuf(4), base, entries_ptr, cover, marks, origin_g, limit_g, x_q, g_squares):
    # One window of a child's SPHINCS list, absorbed exactly as the child absorbed
    # it, but with each block's claim read at a hinted index into THIS node's table
    # and marked in the coverage table. The index is an offset into the SPHINCS
    # region and bounded by that region's size, so a child's claim can only ever
    # land on a SPHINCS slot. Counters as in `sphincs_window`.
    nxt = scaled_log(x_q * GEN, g_squares, const(6 + SIGNERS_WINDOW_LOG))
    st = state
    for j in unroll(0, SIGNERS_WINDOW):
        off_hint = hint_witness("child_sphincs_index")
        assert log(off_hint) < log(limit_g)  # precondition as in the raw loops
        cover[origin_g * off_hint] = marks * GEN ** j
        entry = entries_ptr * off_hint ** 8
        out = StackBuf(4)
        if const(j + 1 == SIGNERS_WINDOW):
            blake2s(entry[0:4], entry[4:8], out, cv=st, md=[nxt, 0])
        else:
            blake2s(entry[0:4], entry[4:8], out, cv=st, md=[base + const(64 * (j + 1)), 0])
        st = out
    return st, nxt




def child_sphincs_list_digest(entries_ptr, cover, base, origin_g, limit_g, n_g, g_squares):
    # BLAKE2s of a child's declared SPHINCS claims, over the same 64n bytes the
    # child hashed (`sphincs_list_digest`), so the digest it rebuilds is the one the
    # child's statement carries. `base` prefixes the coverage write values, which
    # count the claims off as they are marked.
    digest = StackBuf(4)
    if n_g == 1:
        blake2s([0, 0, 0, 0], [0, 0, 0, 0], digest, md=[0, MD_FINAL])
    else:
        split = StackBuf(2)
        hint_witness(split, "signers_split")
        windows = split[0]
        tail = split[1]
        assert log(tail) < SIGNERS_WINDOW
        assert log(windows) < SIGNERS_MAX_WINDOWS
        assert windows ** SIGNERS_WINDOW * tail == n_g * INV_GEN
        chain = HeapBuf((windows * GEN) ** 5)  # state, base
        chain[0:4] = [BLAKE2S_IV_0, BLAKE2S_IV_1, BLAKE2S_IV_2, BLAKE2S_IV_3]
        chain[GEN ** 4] = 0
        for xq in mul_range(1, windows):
            slot = chain * xq ** 5
            marks = base * xq ** SIGNERS_WINDOW
            st, nb = child_sphincs_window(slot[0:4], slot[GEN ** 4], entries_ptr, cover, marks, origin_g, limit_g, xq, g_squares)
            step = slot * GEN ** 5
            step[0:4] = st
            step[GEN ** 4] = nb
        end = chain * windows ** 5
        marks = base * windows ** SIGNERS_WINDOW
        t, unused, unused_marks = tail_blocks(end[0:4], end[GEN ** 4], entries_ptr, cover, marks, origin_g, limit_g, tail, LIST_CHILD_SPHINCS)
        off_hint = hint_witness("child_sphincs_index")
        assert log(off_hint) < log(limit_g)
        cover[origin_g * off_hint] = base * (n_g * INV_GEN)
        entry = entries_ptr * off_hint ** 8
        final = [scaled_log(n_g, g_squares, 6), MD_FINAL]
        blake2s(entry[0:4], entry[4:8], digest, cv=t, md=final)
    return digest


def plain_window(state: StackBuf(4), base, run_ptr, x_q, g_squares):
    # One window over a run of words already in memory, eight to a block, hinting
    # nothing. Counters as in `sphincs_window`.
    nxt = scaled_log(x_q * GEN, g_squares, const(6 + SIGNERS_WINDOW_LOG))
    st = state
    for j in unroll(0, SIGNERS_WINDOW):
        block = run_ptr * GEN ** (8 * j)
        out = StackBuf(4)
        if const(j + 1 == SIGNERS_WINDOW):
            blake2s(block[0:4], block[4:8], out, cv=st, md=[nxt, 0])
        else:
            blake2s(block[0:4], block[4:8], out, cv=st, md=[base + const(64 * (j + 1)), 0])
        st = out
    return st, nxt




def signer_set_digest(run_ptr, n_epochs_g, g_squares):
    # BLAKE2s of the signer set: both list lengths and the SPHINCS list's digest
    # in the first block, then two blocks a group, its (epoch, count, message)
    # and its key list's digest. Every block is full, so the hash is over exactly
    # 64·(1 + 2·epochs) bytes, and leading with both lengths makes the encoding
    # prefix-free: no set's string is a prefix of another's.
    blocks = n_epochs_g * n_epochs_g * GEN  # g^(1 + 2·epochs)
    split = StackBuf(2)
    hint_witness(split, "signers_split")
    windows = split[0]
    tail = split[1]
    assert log(tail) < SIGNERS_WINDOW
    assert log(windows) < SIGNERS_MAX_WINDOWS
    assert windows ** SIGNERS_WINDOW * tail == blocks * INV_GEN
    chain = HeapBuf((windows * GEN) ** 6)
    chain[0:4] = [BLAKE2S_IV_0, BLAKE2S_IV_1, BLAKE2S_IV_2, BLAKE2S_IV_3]
    chain[GEN ** 4] = 0
    chain[GEN ** 5] = run_ptr
    for xq in mul_range(1, windows):
        slot = chain * xq ** 6
        st, nb = plain_window(slot[0:4], slot[GEN ** 4], slot[GEN ** 5], xq, g_squares)
        step = slot * GEN ** 6
        step[0:4] = st
        step[GEN ** 4] = nb
        step[GEN ** 5] = slot[GEN ** 5] * GEN ** (8 * SIGNERS_WINDOW)
    end = chain * windows ** 6
    t, last, unused = tail_blocks(end[0:4], end[GEN ** 4], end[GEN ** 5], 0, 0, 0, 0, tail, LIST_PLAIN)
    final = [scaled_log(blocks, g_squares, 6), MD_FINAL]
    digest = StackBuf(4)
    blake2s(last[0:4], last[4:8], digest, cv=t, md=final)
    return digest


def rebuild_child_groups(nsub_e_g, run_ptr, base, epochs, msgs, group_base, group_slots, n_epochs_g, xmss_table, cover, g_squares):
    # The child's epoch groups, written into the run its own signer-set hash covers,
    # two blocks a group exactly as the child laid them out: its (epoch, count,
    # message), then the digest of its keys, read from THIS node's table through
    # hinted indices. A hinted map ties each group to the parent group holding the
    # same epoch AND message, whose region its keys land in. Everything hinted here
    # is pinned by the digest, which the child's statement carries. The running
    # product of the group counts prefixes each group's coverage writes and ends as
    # the child's XMSS claim count.
    counts = HeapBuf(nsub_e_g * GEN)
    counts[GEN ** 0] = 1
    for xj in mul_range(1, nsub_e_g):
        grp = StackBuf(6)
        hint_witness(grp, "child_group")  # epoch, message (four words), count
        n_keys = grp[5]
        assert log(n_keys) < MAX_KEYS
        parent = hint_witness("child_group_map")
        assert log(parent) < log(n_epochs_g)
        assert epochs[parent] == grp[0]
        parent_msg = msgs * parent ** 4
        parent_msg[0:4] = grp[1:5]
        halves = StackBuf(2)
        hint_witness(halves, "child_halves")
        assert log(halves[1]) < 2
        assert log(halves[0]) < MAX_KEYS
        assert halves[0] * halves[0] * halves[1] == n_keys
        gb = group_base[parent]
        prefix = counts[xj]
        kd = child_key_list_digest(xmss_table * gb ** 4, cover, base * prefix, gb, group_slots[parent], halves[0], halves[1], n_keys, g_squares)
        slot = run_ptr * xj ** 16 * GEN ** 8
        slot[1] = grp[0]
        slot[GEN] = 0
        slot[GEN ** 2] = n_keys
        slot[GEN ** 3] = 0
        slot[4:8] = grp[1:5]
        slot[8:12] = kd
        slot[12:16] = [0, 0, 0, 0]
        counts[xj * GEN] = prefix * n_keys
    return counts[nsub_e_g]


# ================================ LeanDA ===============================
# Hash the encoded rows and the hinted membership vector, then check their inner products.
# The external verifier derives the vector hash from the root; recursion preserves both.


def da_verify(g_squares):
    # Returns the matrix root and membership-vector hash, four words each.
    # The row count is a run-time parameter. The trees need a compile-time depth,
    # so the rows are padded to a power of two and the two `match`es below dispatch
    # on its log; everything else walks the real rows only. A padding row is the
    # zero codeword, so its cell digest and its row digest are constants, and the
    # gap loop writes them without hashing anything.
    shape = StackBuf(2)
    hint_witness(shape, "da_shape")  # n_blob, then log2 of the padded count
    n_blob_g = shape[0]
    g_log_pad = shape[1]
    n_pad_g, gap_g = da_row_shape(n_blob_g, g_log_pad, g_squares)

    prefix_digests = HeapBuf(n_pad_g ** (4 * DA_PREFIX_CELLS))
    prefix_bases = HeapBuf(n_blob_g)
    for xi in mul_range(1, n_blob_g):
        prefix_bases[xi] = prefix_digests * xi ** (4 * DA_PREFIX_CELLS)

    hashes = HeapBuf(4 * (DA_CELLS + 1))
    hashes[0:4] = [BLAKE2S_IV_0, BLAKE2S_IV_1, BLAKE2S_IV_2, BLAKE2S_IV_3]
    counter_values = StackBuf(3 * DA_CELLS + 1)
    for w in unroll(0, 3 * DA_CELLS + 1):
        counter_values[w] = const(w * 2 ** (DA_LOG_CELL + 3))
    counters = addr(counter_values)

    # Each row's running sum uses a fresh write-once element per column.
    acc = HeapBuf(n_blob_g ** (3 * (DA_CELLS + 1)))
    rowbase = HeapBuf(n_blob_g)
    for xi in mul_range(1, n_blob_g):
        chain = acc * xi ** (3 * (DA_CELLS + 1))
        rowbase[xi] = chain
        chain[0:3] = ZERO

    # Prefix blocks first, so the digests the row branch needs are stored by a
    # loop that knows it is inside the prefix, with no per-block branch.
    coltree = HeapBuf(8 * DA_CELLS)
    for xb in mul_range(1, GEN ** DA_PREFIX_CELLS):
        da_verify_column(xb, n_blob_g, n_pad_g, gap_g, g_log_pad, prefix_bases, coltree, rowbase, hashes, counters, 1)
    for xb in mul_range(GEN ** DA_PREFIX_CELLS, GEN ** DA_CELLS):
        da_verify_column(xb, n_blob_g, n_pad_g, gap_g, g_log_pad, prefix_bases, coltree, rowbase, hashes, counters, 0)

    for xi in mul_range(1, n_blob_g):
        chain = rowbase[xi]
        k = 3 * DA_CELLS
        assert_eq192(chain[k:k + 3], ZERO)
    col_root = da_levels(coltree, DA_CELLS, DA_BLOCK_BITS)

    # The row branch: each row's prefix digests, hashed as one string.
    rowtree = HeapBuf(n_pad_g ** 8)
    for xi in mul_range(1, n_blob_g):
        prefix = prefix_bases[xi]
        st = StackBuf(4)
        blake2s(prefix[0:4], prefix[4:8], st, counter=64, final=1 // DA_ROW_BLOCKS)
        for b in unroll(1, DA_ROW_BLOCKS):
            nxt = StackBuf(4)
            blake2s(prefix[8 * b:8 * b + 4], prefix[8 * b + 4:8 * b + 8], nxt, cv=st, counter=64 * (b + 1), final=(b + 1) // DA_ROW_BLOCKS)
            st = nxt
        slot = rowtree * xi ** 4
        slot[0:4] = st
    for xd in mul_range(1, gap_g):
        pad = rowtree * n_blob_g ** 4 * xd ** 4
        pad[0:4] = [DA_PAD_ROW[0], DA_PAD_ROW[1], DA_PAD_ROW[2], DA_PAD_ROW[3]]
    row_root = match(log(g_log_pad), range(0, DA_TREE_ARMS), lambda k: da_levels(rowtree, 2 ** k, k))

    root = StackBuf(4)
    blake2s(row_root, col_root, root)
    vec = 4 * DA_CELLS
    return root, hashes[vec:vec + 4]


def da_row_shape(n_blob_g, g_log_pad, g_squares):
    assert n_blob_g != 1
    assert log(n_blob_g) < DA_MAX_ROWS + 1
    assert log(g_log_pad) < DA_LOG_MAX_ROWS + 1
    n_pad_g = g_squares[g_log_pad]
    # n_blob <= n_pad < 2*n_blob: both differences must be nonnegative.
    gap_g = n_pad_g / n_blob_g
    assert log(gap_g) < DA_MAX_ROWS + 1
    assert log(n_blob_g * n_blob_g / (n_pad_g * GEN)) < DA_MAX_ROWS
    return n_pad_g, gap_g


def da_verify_column(xb, n_blob_g, n_pad_g, gap_g, g_log_pad, prefix_bases, coltree, rowbase, hashes, counters, store: Const):
    st = hashes * xb ** 4
    h, lvals = da_vector_dispatch(xb, st[0:4], counters)
    nxt = st * GEN ** 4
    nxt[0:4] = h
    node = HeapBuf(n_pad_g ** 8)
    xb3 = xb ** 3
    for xi in mul_range(1, n_blob_g):
        d, s = da_verify_cell(lvals)
        chain = rowbase[xi] * xb3
        chain[3:6] = add192(chain[0:3], s)
        leaf = node * xi ** 4
        leaf[0:4] = d
        if const(store == 1):
            slot = prefix_bases[xi] * xb ** 4
            slot[0:4] = d
    for xd in mul_range(1, gap_g):
        pad = node * n_blob_g ** 4 * xd ** 4
        pad[0:4] = [DA_PAD_CELL[0], DA_PAD_CELL[1], DA_PAD_CELL[2], DA_PAD_CELL[3]]
    c = match(log(g_log_pad), range(0, DA_TREE_ARMS), lambda k: da_levels(node, 2 ** k, k))
    out = coltree * xb ** 4
    out[0:4] = c
    return


def da_verify_cell(lvals):
    # The symbols are words, so the hash and the dot product read them directly; the
    # weights are elements, three words each, so the dot product runs limb by limb.
    sym = StackBuf(DA_CELL)
    hint_witness(sym, "da_symbols")
    s0 = 0
    s1 = 0
    s2 = 0
    for e in unroll(0, DA_CELL):
        k = 3 * e
        sv = sym[e]
        s0 += sv * lvals[GEN ** k]
        s1 += sv * lvals[GEN ** (k + 1)]
        s2 += sv * lvals[GEN ** (k + 2)]
    st = StackBuf(4)
    blake2s(sym[0:4], sym[4:8], st, counter=64, final=1 // DA_CELL_BLOCKS)
    for b in unroll(1, DA_CELL_BLOCKS):
        nxt = StackBuf(4)
        blake2s(sym[8 * b:8 * b + 4], sym[8 * b + 4:8 * b + 8], nxt, cv=st, counter=64 * (b + 1), final=(b + 1) // DA_CELL_BLOCKS)
        st = nxt
    return st, [s0, s1, s2]


def da_levels(tree, n: Const, log_n: Const):
    # The internal levels of a Merkle tree whose leaves already sit at level 0 of
    # `tree` (4 words a node, level lvl at 8n - 8n//2**lvl). Returns the root.
    for lvl in unroll(0, log_n):
        for xp in mul_range(1, GEN ** (n // 2 ** (lvl + 1))):
            a = tree * GEN ** (8 * n - 8 * n // 2 ** lvl) * xp ** 8
            b = tree * GEN ** (8 * n - 8 * n // 2 ** (lvl + 1)) * xp ** 4
            blake2s(a[0:4], a[4:8], b[0:4])
    root = 8 * n - 8
    return tree[root:root + 4]


def da_vector_dispatch(xb, h: StackBuf(4), counters):
    out = StackBuf(4)
    weights = StackBuf(1)
    if xb == GEN ** (DA_CELLS - 1):
        a, w = da_vector_cell(xb, h, counters, 1)
        out[0:4] = a
        weights[0] = w
    else:
        a, w = da_vector_cell(xb, h, counters, 0)
        out[0:4] = a
        weights[0] = w
    return out, weights[0]


def da_vector_cell(xb, h: StackBuf(4), counters, final: Const):
    weights = StackBuf(3 * DA_CELL)
    hint_witness(weights, "da_weights")
    st = h
    # Three power-of-two byte windows per cell keep counter offsets disjoint from the base.
    base = counters[xb ** 3]
    for w in unroll(0, 3):
        window = xb ** 3 * GEN ** w
        end = counters[window * GEN]
        for b in unroll(0, DA_CELL_BLOCKS):
            out = StackBuf(4)
            if const(b + 1 == DA_CELL_BLOCKS):
                counter = end
            else:
                counter = base + const(64 * (b + 1))
            flags = 0
            if const(final == 1):
                if const(w == 2):
                    if const(b + 1 == DA_CELL_BLOCKS):
                        flags = MD_FINAL
            lo = w * DA_CELL + 8 * b
            blake2s(weights[lo:lo + 4], weights[lo + 4:lo + 8], out, cv=st, md=[counter, flags])
            st = out
        base = end
    weights_ptr = addr(weights)
    return st, weights_ptr

# ================================ the aggregation node ==============================


def da_list_digest(roots, n_g):
    # At most 16 roots: every BLAKE2s byte counter and final flag is constant.
    digest = match(log(n_g), range(0, DA_ROOT_COUNTS), lambda n: da_hash_roots(roots, n))
    return digest


def da_hash_roots(roots, n: Const):
    digest = StackBuf(4)
    if const(n == 0):
        blake2s([0, 0, 0, 0], [0, 0, 0, 0], digest, counter=0, final=1)
    else:
        blake2s(roots[0:4], roots[4:8], digest, counter=64, final=1 // n)
        for i in unroll(1, n):
            claim = roots * GEN ** (8 * i)
            out = StackBuf(4)
            blake2s(claim[0:4], claim[4:8], out, cv=digest, counter=64 * (i + 1), final=(i + 1) // n)
            digest = out
    return digest


def cover_da_root(roots, cover, n_slots_g, mark):
    # Marks one DA slot and returns its eight words: the root, then the vector hash.
    index = hint_witness("da_index")
    assert log(index) < log(n_slots_g)
    cover[index] = mark
    return roots * index ** 8


def main():
    # One node of an aggregation tree: raw XMSS signatures grouped by the epoch they
    # were made at (a RUNTIME number of groups), n_raw_sphincs SPHINCS signatures
    # and n_children sub-proofs OF THIS SAME BYTECODE. Each XMSS group carries its
    # own (epoch, message) pair, and each SPHINCS signature is against the message
    # in its own coverage slot. DA roots occupy a separate region of the same table.
    #
    # The declared lists are the signer set; the duplicate slots absorb keys a child
    # covers that the set does not declare. The coverage table is one region per
    # epoch group, each its declared keys then its own duplicates, then SPHINCS
    # and DA regions shaped the same way:
    #
    #   [group 0: declared | dup]...[group n_epochs-1: declared | dup][SPHINCS: declared | dup][DA: declared | dup]
    #
    # The first n_decl groups are the signer set's; the n_drop after them declare
    # nothing, holding a child group's (epoch, message) without publishing it.
    #
    # so one range check per write keeps each writer inside its own region: that is
    # what makes the statement's split mean which scheme verified which key against
    # which (epoch, message). An XMSS slot is four words, a SPHINCS slot eight: a key
    # and the message that key signed. A DA root occupies eight words.
    meta = StackBuf(7)
    hint_witness(meta, "meta")  # every count in the exponent
    n_decl_g = meta[0]
    n_drop_g = meta[1]
    n_sphincs_g = meta[2]
    n_sdup_g = meta[3]
    n_raw_s_g = meta[4]
    n_children_g = meta[5]
    n_direct_da_g = meta[6]
    # Declared plus dropped, so bounding each side pins n_decl <= n_epochs.
    assert log(n_decl_g) < MAX_EPOCHS + 1
    assert log(n_drop_g) < MAX_EPOCHS + 1
    n_epochs_g = n_decl_g * n_drop_g
    assert log(n_epochs_g) < MAX_EPOCHS + 1
    assert log(n_sphincs_g) < MAX_KEYS
    assert log(n_sdup_g) < MAX_KEYS
    assert log(n_raw_s_g) < MAX_KEYS
    assert log(n_children_g) < MAX_RECURSIONS + 1
    assert log(n_direct_da_g) < 2
    da_meta = StackBuf(2)
    hint_witness(da_meta, "da_meta")
    n_da_g = da_meta[0]
    n_da_dup_g = da_meta[1]
    assert log(n_da_g) < MAX_DA_ROOTS + 1
    assert log(n_da_dup_g) < MAX_RECURSIONS * MAX_DA_ROOTS + 2
    da_slots_g = n_da_g * n_da_dup_g
    assert log(da_slots_g) < MAX_RECURSIONS * MAX_DA_ROOTS + 2

    # ---- the epoch groups: geometry pass ----
    # Per group: its epoch, its four message words, and its declared, duplicate and
    # raw-signature counts, each count bounded before it enters a product (up to
    # 2^16 factors of exponent < 2^17 stay far from the order 2^64 - 1, so nothing
    # wraps). Region bases and the three totals ride a stride-4 chain; the per-group
    # values land in heap buffers the later passes and the children's hinted group
    # maps read back at runtime.
    epochs = HeapBuf(n_epochs_g)
    msgs = HeapBuf(n_epochs_g ** 4)
    group_n_keys = HeapBuf(n_epochs_g)
    group_n_dups = HeapBuf(n_epochs_g)
    group_n_raw = HeapBuf(n_epochs_g)
    group_base = HeapBuf(n_epochs_g)
    group_slots = HeapBuf(n_epochs_g)
    geo = HeapBuf((n_epochs_g * GEN) ** 4)  # [base, n_xmss product, n_raw product]
    geo[1] = 1
    geo[GEN] = 1
    geo[GEN ** 2] = 1
    for xe in mul_range(1, n_epochs_g):
        grp = StackBuf(8)
        hint_witness(grp, "group")  # epoch, message (four words), n, n_dup, n_raw
        assert log(grp[5]) < MAX_KEYS
        assert log(grp[6]) < MAX_KEYS
        assert log(grp[7]) < MAX_KEYS
        epochs[xe] = grp[0]
        msg = msgs * xe ** 4
        msg[0:4] = grp[1:5]
        group_n_keys[xe] = grp[5]
        group_n_dups[xe] = grp[6]
        group_n_raw[xe] = grp[7]
        state = geo * xe ** 4
        base = state[1]
        group_base[xe] = base
        slots = grp[5] * grp[6]
        group_slots[xe] = slots
        nxt = geo * (xe * GEN) ** 4
        nxt[1] = base * slots
        nxt[GEN] = state[GEN] * grp[5]
        nxt[GEN ** 2] = state[GEN ** 2] * grp[7]
    geo_end = geo * n_epochs_g ** 4
    xmss_slots_g = geo_end[1]
    n_raw_x_g = geo_end[GEN ** 2]
    sphincs_slots_g = n_sphincs_g * n_sdup_g
    # The sum of every region bounds the coverage indices, so it is what has to sit
    # below the minimum memory size.
    da_base_g = xmss_slots_g * sphincs_slots_g
    n_total_g = da_base_g * da_slots_g
    assert log(n_total_g) < MAX_KEYS

    # The proving environment (flock's R1CS and this bytecode) as one digest. It
    # rides the statement rather than the bytecode, so nothing here has to know its
    # own hash; the outer verifier pins it, and every child statement rebuilt below
    # copies it, which is what keeps a whole tree on one bytecode. It lives on the
    # heap, where the loops over children can reach it.
    seed = HeapBuf(4)
    hint_witness(seed[0:4], "fs_seed")

    # ---- the signer set ----
    g_logs_pow2, g_squares = exponent_tables()

    # ---- data availability ----
    da_roots = HeapBuf(da_slots_g ** 8)
    for xd in mul_range(1, da_slots_g):
        root = da_roots * xd ** 8
        hint_witness(root[0:8], "da_roots")
    da_digest = da_list_digest(da_roots, n_da_g)
    # One table per scheme, the XMSS one an epoch group at a time: each group its
    # declared list (strictly sorted, checked by the outer verifier, which holds it)
    # followed by its own duplicate slots. The coverage indices below run over one
    # space: the group regions in order, then SPHINCS, then DA.
    #
    # The digest is a plain BLAKE2s of one string, in whole blocks: both lengths
    # and the SPHINCS list's digest, then per group its (epoch, count,
    # message) and its key list's digest, each list hashed plainly in turn. Leading
    # with both lengths makes the encoding prefix-free, so no set's string is a
    # prefix of another's and the digest binds its own lengths. `half` and `odd` are
    # hinted per group and pinned by half*half*odd == n with odd in {0, 1}, which
    # leaves half = n // 2 and odd = n % 2 as the only solution.
    xmss_table = HeapBuf(xmss_slots_g ** 4)
    sphincs_table = HeapBuf(sphincs_slots_g ** 8)
    # The run the set's hash covers: both lengths and the SPHINCS list's digest
    # in one block, then two a group. Sixteen words a group, so a group's
    # header and its key digest are one block each.
    signers_run = HeapBuf(n_decl_g ** 16 * GEN ** 8)
    signers_run[1] = n_decl_g
    signers_run[GEN] = 0
    signers_run[GEN ** 2] = n_sphincs_g
    signers_run[GEN ** 3] = 0
    decl_keys = HeapBuf(n_decl_g * GEN)
    decl_keys[GEN ** 0] = 1
    for xe in mul_range(1, n_decl_g):
        n_keys = group_n_keys[xe]
        base = group_base[xe]
        decl_keys[xe * GEN] = decl_keys[xe] * n_keys
        halves = StackBuf(2)
        hint_witness(halves, "pk_halves")
        assert log(halves[1]) < 2
        assert log(halves[0]) < MAX_KEYS
        assert halves[0] * halves[0] * halves[1] == n_keys
        kd = key_list_digest(xmss_table * base ** 4, halves[0], halves[1], n_keys, g_squares)
        group_msg = msgs * xe ** 4
        slot = signers_run * xe ** 16 * GEN ** 8
        slot[1] = epochs[xe]
        slot[GEN] = 0
        slot[GEN ** 2] = n_keys
        slot[GEN ** 3] = 0
        slot[4:8] = group_msg[0:4]
        slot[8:12] = kd
        slot[12:16] = [0, 0, 0, 0]
    # The duplicate slots ride the same table but outside the hashed prefix, past
    # each group's declared keys. Over the whole table: a dropped group has only these.
    for xe in mul_range(1, n_epochs_g):
        n_keys = group_n_keys[xe]
        base = group_base[xe]
        dup_ptr = xmss_table * (base * n_keys) ** 4
        for xd in mul_range(1, group_n_dups[xe]):
            dup = dup_ptr * xd ** 4
            hint_witness(dup[0:4], "dup_pubkeys")
    sp_digest = sphincs_list_digest(sphincs_table, n_sphincs_g, g_squares)
    signers_run[4:8] = sp_digest
    # At least one published signature claim or DA root also ensures a nonempty coverage table.
    assert decl_keys[n_decl_g] * n_sphincs_g * n_da_g != 1
    signers_hash = signer_set_digest(signers_run, n_decl_g, g_squares)
    for xd in mul_range(1, n_sdup_g):
        dup = sphincs_table * (n_sphincs_g * xd) ** 8
        hint_witness(dup[0:8], "dup_sphincs")

    # ---- coverage ----
    # Every one of the n_total slots is written exactly once: write-once memory
    # rejects a second write (the value written is the running count, so two writes
    # to one slot disagree), and the count below rejects a missed one. So every
    # declared claim is covered by a direct check of its own kind or by a verified
    # child. Each writer is confined to its own region, including DA roots.
    # The raw XMSS walk runs one loop per epoch group, each signature verified
    # against that group's index words (built here, only for a group that holds raw
    # signatures); a stride-1 chain threads the running count across the groups.
    cover = HeapBuf(n_total_g)
    da_cover = cover * da_base_g
    merkle_bits = HeapBuf(n_epochs_g ** LOG_LIFETIME)
    index_tables = HeapBuf(n_epochs_g ** (LOG_LIFETIME + 1))
    raw_count = HeapBuf(n_epochs_g * GEN)
    raw_count[GEN ** 0] = 1
    for xe in mul_range(1, n_epochs_g):
        n_raw = group_n_raw[xe]
        prefix = raw_count[xe]
        if n_raw != 1:
            index_table = index_tables * xe ** (LOG_LIFETIME + 1)
            group_bits = merkle_bits * xe ** LOG_LIFETIME
            fill_xmss_epoch_tables(epochs[xe], group_bits, index_table)
            slots = group_slots[xe]
            base = group_base[xe]
            keys = xmss_table * base ** 4
            group_msg = msgs * xe ** 4
            for xi in mul_range(1, n_raw):
                idx = hint_witness("raw_index")
                # A runtime bound, whose `n_total < 2^MIN_LOG_MEM` precondition is
                # discharged by `assert log(n_total_g) < MAX_KEYS` above. Without it
                # this degenerates to what DEREF alone gives and an index could
                # reach past `cover`, which is the whole bijection. The bound is
                # this GROUP's region, so a signature verified at this (epoch,
                # message) covers no other group's declared key.
                assert log(idx) < log(slots)
                cover[base * idx] = prefix * xi
                verify_sig(group_msg, index_table, group_bits, keys * idx ** 4)
            raw_count[xe * GEN] = prefix * n_raw
        else:
            raw_count[xe * GEN] = prefix
    for xj in mul_range(1, n_raw_s_g):
        off_hint = hint_witness("sp_raw_index")
        assert log(off_hint) < log(sphincs_slots_g)
        cover[xmss_slots_g * off_hint] = n_raw_x_g * xj
        verify_sig_sphincs(sphincs_table * off_hint ** 8)

    if n_direct_da_g == GEN:
        da_root, da_vector = da_verify(g_squares)
        expected = cover_da_root(da_roots, da_cover, da_slots_g, n_raw_x_g * n_raw_s_g)
        expected[0:4] = da_root
        expected[4:8] = da_vector

    # ---- children ----
    child_pi = HeapBuf(n_children_g ** 4)
    child_fresh = HeapBuf(n_children_g ** (3 * DEFER_SIZE))
    child_carried = HeapBuf(n_children_g ** (3 * DEFER_STMT_CELLS))
    written = HeapBuf(n_children_g * GEN)  # loop-carried write count, one per child
    written[GEN ** 0] = n_raw_x_g * n_raw_s_g * n_direct_da_g
    for xc in mul_range(1, n_children_g):
        base = written[xc]
        # The child's two list lengths, then its groups, rebuilt into its signer-set
        # run by rebuild_child_groups: everything hinted there is pinned by the
        # run's hash, which the child's statement digest carries, so a lie about any
        # of it changes the public input its proof has to satisfy. Nothing demands a
        # mid-tree statement be canonical (sorted, distinct groups); it still binds
        # every claim to its (epoch, message), which is all the group map relies on.
        child_meta = StackBuf(2)
        hint_witness(child_meta, "child_meta")  # n_epochs, n_sphincs
        nsub_e_g = child_meta[0]
        nsub_s_g = child_meta[1]
        assert log(nsub_e_g) < MAX_EPOCHS + 1
        assert log(nsub_s_g) < MAX_KEYS
        sub_run = HeapBuf(nsub_e_g ** 16 * GEN ** 8)
        sub_run[1] = nsub_e_g
        sub_run[GEN] = 0
        sub_run[GEN ** 2] = nsub_s_g
        sub_run[GEN ** 3] = 0
        nsub_x_g = rebuild_child_groups(nsub_e_g, sub_run, base, epochs, msgs, group_base, group_slots, n_epochs_g, xmss_table, cover, g_squares)
        # Implied by the per-group bounds and the child's own n_total assert; stands
        # as documentation.
        assert log(nsub_x_g) < MAX_KEYS
        nsub_g = nsub_x_g * nsub_s_g
        csp = child_sphincs_list_digest(sphincs_table, cover, base * nsub_x_g, xmss_slots_g, sphincs_slots_g, nsub_s_g, g_squares)
        sub_run[4:8] = csp
        sub_hash = signer_set_digest(sub_run, nsub_e_g, g_squares)
        carried = child_carried * xc ** (3 * DEFER_STMT_CELLS)
        hint_witness(carried[0:3 * DEFER_STMT_CELLS], "child_defer")
        nsub_da_g = hint_witness("child_da_count")
        assert log(nsub_da_g) < MAX_DA_ROOTS + 1
        child_da = HeapBuf(nsub_da_g ** 8)
        for xd in mul_range(1, nsub_da_g):
            covered = cover_da_root(da_roots, da_cover, da_slots_g, base * nsub_g * xd)
            slot = child_da * xd ** 8
            slot[0:8] = covered[0:8]
        child_da_digest = da_list_digest(child_da, nsub_da_g)
        pi = statement_digest(seed, sub_hash, child_da_digest, carried)
        pi_slot = child_pi * xc ** 4
        pi_slot[0:4] = pi
        verify_sub(pi, seed, g_logs_pow2, g_squares, child_fresh * xc ** (3 * DEFER_SIZE))
        written[xc * GEN] = base * nsub_g * nsub_da_g
    assert written[n_children_g] == n_total_g

    # ---- this node's own deferred claims ----
    defer_stmt = HeapBuf(3 * DEFER_STMT_CELLS)
    if n_children_g == 1:
        # A leaf has nothing to batch, so it defers the three fixed polynomials at
        # the all-zeros point. Their values ride a hint and are checked nowhere
        # here: the outer verifier recomputes them and rebuilds the statement, so a
        # lie changes the public input rather than the claim.
        leaf_values = StackBuf(9)
        hint_witness(leaf_values, "leaf_defer")
        for k in unroll(0, BYTECODE_VARS):
            c = 3 * k
            defer_stmt[c:c + 3] = ZERO
        k = 3 * DEFER_STMT_BC_VALUE
        defer_stmt[k:k + 3] = leaf_values[0:3]
        for j in unroll(0, 2 * K_LOG):
            c = 3 * (DEFER_STMT_MAT_POINT + j)
            defer_stmt[c:c + 3] = ZERO
        k = 3 * DEFER_STMT_A_VALUE
        defer_stmt[k:k + 3] = leaf_values[3:6]
        k = 3 * DEFER_STMT_B_VALUE
        defer_stmt[k:k + 3] = leaf_values[6:9]
    else:
        aggregate_claims(n_children_g, child_pi, child_fresh, child_carried, defer_stmt)

    own = statement_digest(seed, signers_hash, da_digest, defer_stmt)
    pub = GEN ** 0
    pub[0:4] = own
    return


def aggregate_claims(n_children_g, child_pi, child_fresh, child_carried, defer_stmt):
    # Every child contributes two claims per fixed polynomial: the one IT deferred
    # (carried in its statement) and the fresh one raised by verifying its proof. A
    # fresh transcript binds all of them, samples the batching coefficients, and two
    # sumchecks (one for the bytecode, one shared by the two matrices) reduce the
    # lot to one claim each, which is what the node then defers in its own
    # statement.
    #
    # A carried claim is a plain point, so its weight is an eq product; a fresh one
    # carries flock's zerocheck/lincheck structure and keeps the succinct weight the
    # sub-verifier exported. That is the only asymmetry.
    bc_msgs = HeapBuf(6 * BYTECODE_VARS)
    hint_witness(bc_msgs[0:6 * BYTECODE_VARS], "bc_sumcheck_msgs")
    mat_msgs = HeapBuf(12 * K_LOG)
    hint_witness(mat_msgs[0:12 * K_LOG], "mat_sumcheck_msgs")
    bytecode_star = StackBuf(3)
    hint_witness(bytecode_star, "bc_star_hint")
    mat_stars = StackBuf(6)
    hint_witness(mat_stars, "mat_stars_hint")

    # ---- one transcript over every child's statement and both its claim sets ----
    # A child's public input is observed as two scalars, a 128-bit half each.
    fresh_row = HeapBuf(n_children_g)
    carried_row = HeapBuf(n_children_g)
    agg_fs = obs([AGG_SEED_0, AGG_SEED_1, AGG_SEED_2, AGG_SEED_3], [n_children_g, 0, 0])
    absorb = HeapBuf((n_children_g * GEN) ** FS_SLOTS)
    absorb[0:4] = agg_fs
    for xc in mul_range(1, n_children_g):
        row = absorb * xc ** FS_SLOTS
        pi = child_pi * xc ** 4
        st = obs(row[0:4], [pi[1], pi[GEN], 0])
        st = obs(st, [pi[GEN ** 2], pi[GEN ** 3], 0])
        fresh = child_fresh * xc ** (3 * DEFER_SIZE)
        fresh_row[xc] = fresh
        for k in unroll(0, DEFER_SIZE):
            st = obs_at(st, fresh * GEN ** (3 * k))
        carried = child_carried * xc ** (3 * DEFER_STMT_CELLS)
        carried_row[xc] = carried
        for k in unroll(0, DEFER_STMT_CELLS):
            st = obs_at(st, carried * GEN ** (3 * k))
        row[4:8] = st
    absorbed = absorb * n_children_g ** FS_SLOTS

    # ---- bytecode batching sumcheck (BYTECODE_VARS variables, 2 per child) ----
    # Fresh and carried share the bytecode layout (point, then value), so the two
    # differ only in which buffer they come from.
    lam_bc = HeapBuf(n_children_g ** 6)
    bc_chain = HeapBuf((n_children_g * GEN) ** ACC_SLOTS)
    bc_chain[0:4] = absorbed[0:4]
    bc_chain[ACC_VALUE:ACC_VALUE + 3] = ZERO
    for xc in mul_range(1, n_children_g):
        row = bc_chain * xc ** ACC_SLOTS
        st, lam_fresh = squeeze(row[0:4])
        st, lam_carried = squeeze(st)
        pair = lam_bc * xc ** 6
        pair[0:3] = lam_fresh
        pair[3:6] = lam_carried
        fresh = fresh_row[xc]
        carried = carried_row[xc]
        nxt = row * GEN ** ACC_SLOTS
        nxt[0:4] = st
        fb = 3 * FRESH_BC_VALUE
        cb = 3 * DEFER_STMT_BC_VALUE
        nxt[ACC_VALUE:ACC_VALUE + 3] = add192(row[ACC_VALUE:ACC_VALUE + 3], add192(mul192(lam_fresh, fresh[fb:fb + 3]), mul192(lam_carried, carried[cb:cb + 3])))
    bc_end = bc_chain * n_children_g ** ACC_SLOTS
    bc_point = HeapBuf(3 * BYTECODE_VARS)
    agg_fs, bc_running = batch_sumcheck(bc_end[0:4], bc_msgs, bc_end[ACC_VALUE:ACC_VALUE + 3], bc_point, BYTECODE_VARS)
    bc_wsum = HeapBuf((n_children_g * GEN) ** 3)
    bc_wsum[0:3] = ZERO
    for xc in mul_range(1, n_children_g):
        fresh = fresh_row[xc]
        carried = carried_row[xc]
        eq_fresh = ONE
        eq_carried = ONE
        for k in unroll(0, BYTECODE_VARS):
            c = 3 * k
            rk = bc_point[c:c + 3]
            eq_fresh = mul192(eq_fresh, add192(ONE, add192(fresh[c:c + 3], rk)))
            eq_carried = mul192(eq_carried, add192(ONE, add192(carried[c:c + 3], rk)))
        pair = lam_bc * xc ** 6
        x3 = xc ** 3
        nxt = x3 * GEN ** 3
        bc_wsum[nxt:nxt + 3] = add192(bc_wsum[x3:x3 + 3], add192(mul192(pair[0:3], eq_fresh), mul192(pair[3:6], eq_carried)))
    ws_end = n_children_g ** 3
    assert_eq192(bc_running, mul192(bytecode_star, bc_wsum[ws_end:ws_end + 3]))

    # ---- matrix batching sumcheck (2*K_LOG variables, 3 claims per child) ----
    # The fresh claim is one value against A0 weighted by lincheck's alpha plus B0;
    # a carried claim is one value per matrix at a shared point.
    lam_mat = HeapBuf(n_children_g ** 9)
    mat_chain = HeapBuf((n_children_g * GEN) ** ACC_SLOTS)
    mat_chain[0:4] = agg_fs
    mat_chain[ACC_VALUE:ACC_VALUE + 3] = ZERO
    for xc in mul_range(1, n_children_g):
        row = mat_chain * xc ** ACC_SLOTS
        st, lam_fresh = squeeze(row[0:4])
        st, lam_a = squeeze(st)
        st, lam_b = squeeze(st)
        triple = lam_mat * xc ** 9
        triple[0:3] = lam_fresh
        triple[3:6] = lam_a
        triple[6:9] = lam_b
        fresh = fresh_row[xc]
        carried = carried_row[xc]
        nxt = row * GEN ** ACC_SLOTS
        nxt[0:4] = st
        fm = 3 * FRESH_MATPART
        ca = 3 * DEFER_STMT_A_VALUE
        cb = 3 * DEFER_STMT_B_VALUE
        nxt[ACC_VALUE:ACC_VALUE + 3] = add192(row[ACC_VALUE:ACC_VALUE + 3], add192(mul192(lam_fresh, fresh[fm:fm + 3]), add192(mul192(lam_a, carried[ca:ca + 3]), mul192(lam_b, carried[cb:cb + 3]))))
    mat_end = mat_chain * n_children_g ** ACC_SLOTS
    mat_point = HeapBuf(3 * 2 * K_LOG)
    agg_fs, mat_running = batch_sumcheck(mat_end[0:4], mat_msgs, mat_end[ACC_VALUE:ACC_VALUE + 3], mat_point, 2 * K_LOG)
    # Terminal weights. A fresh claim's is U_t(r*) = urow_t(r*_row) * wcol_t(r*_col),
    # with row_weight = (sum_i L_i(zz_t) eq(r*[0..6], i)) * eq(zchi_t, r*[6..K_LOG])
    # and col_weight = (sum_i z_partial_t[i] eq(r*[K_LOG..K_LOG+6], i)) * prod_j (1 +
    # lrr_j + r*[2*K_LOG-1-j]) (the lincheck binds column variables top-down). A
    # carried claim's is a plain eq over all 2*K_LOG coordinates.
    eq_rows = HeapBuf(3 * (2 ** (K_SKIP + 1) - 2))
    eqtree(mat_point, eq_rows, K_SKIP)
    eq_cols = HeapBuf(3 * (2 ** (K_SKIP + 1) - 2))
    eqtree(mat_point * GEN ** (3 * K_LOG), eq_cols, K_SKIP)
    w_sums = HeapBuf((n_children_g * GEN) ** 6)  # the A and B weight sums
    w_sums[0:3] = ZERO
    w_sums[3:6] = ZERO
    for xc in mul_range(1, n_children_g):
        fresh = fresh_row[xc]
        row_nums = StackBuf(3 * 2 ** K_SKIP)
        zs = 3 * FRESH_Z_SKIP
        lag64(fresh[zs:zs + 3], row_nums, 0)
        row_weight = ZERO
        for i in unroll(0, 2 ** K_SKIP):
            k = 3 * i
            e = 3 * (2 ** K_SKIP - 2 + i)
            row_weight = add192(row_weight, mul192(row_nums[k:k + 3], eq_rows[e:e + 3]))
        row_weight = mul192(row_weight, LAGRANGE_INV_S)
        for k in unroll(0, LINCHECK_ROUNDS):
            zc = 3 * (FRESH_ZCHI + k)
            mp = 3 * (K_SKIP + k)
            row_weight = mul192(row_weight, add192(ONE, add192(fresh[zc:zc + 3], mat_point[mp:mp + 3])))
        col_weight = ZERO
        for i in unroll(0, 2 ** K_SKIP):
            zp = 3 * (FRESH_Z_PARTIAL + i)
            e = 3 * (2 ** K_SKIP - 2 + i)
            col_weight = add192(col_weight, mul192(fresh[zp:zp + 3], eq_cols[e:e + 3]))
        for j in unroll(0, LINCHECK_ROUNDS):
            lr = 3 * (FRESH_LINCHECK_RS + j)
            mp = 3 * (2 * K_LOG - 1 - j)
            col_weight = mul192(col_weight, add192(ONE, add192(fresh[lr:lr + 3], mat_point[mp:mp + 3])))
        weight_u = mul192(row_weight, col_weight)
        carried = carried_row[xc]
        eq_carried = ONE
        for k in unroll(0, 2 * K_LOG):
            cp = 3 * (DEFER_STMT_MAT_POINT + k)
            mp = 3 * k
            eq_carried = mul192(eq_carried, add192(ONE, add192(carried[cp:cp + 3], mat_point[mp:mp + 3])))
        triple = lam_mat * xc ** 9
        lam_fresh = triple[0:3]
        fa = 3 * FRESH_ALPHA
        row = w_sums * xc ** 6
        row[6:9] = add192(row[0:3], add192(mul192(lam_fresh, weight_u), mul192(triple[3:6], eq_carried)))
        row[9:12] = add192(row[3:6], add192(mul192(mul192(lam_fresh, fresh[fa:fa + 3]), weight_u), mul192(triple[6:9], eq_carried)))
    w_end = w_sums * n_children_g ** 6
    assert_eq192(mat_running, add192(mul192(mat_stars[0:3], w_end[0:3]), mul192(mat_stars[3:6], w_end[3:6])))

    for k in unroll(0, BYTECODE_VARS):
        c = 3 * k
        defer_stmt[c:c + 3] = bc_point[c:c + 3]
    k = 3 * DEFER_STMT_BC_VALUE
    defer_stmt[k:k + 3] = bytecode_star
    for j in unroll(0, 2 * K_LOG):
        c = 3 * j
        d = 3 * (DEFER_STMT_MAT_POINT + j)
        defer_stmt[d:d + 3] = mat_point[c:c + 3]
    k = 3 * DEFER_STMT_A_VALUE
    defer_stmt[k:k + 3] = mat_stars[0:3]
    k = 3 * DEFER_STMT_B_VALUE
    defer_stmt[k:k + 3] = mat_stars[3:6]
    return
