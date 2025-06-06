//! Lemon: A LALR(1) Parser Generator, in Zig
//!
//! This file is a faithful translation of D. Richard Hipp's Lemon
//! parser into Zig.  The goal is to produce a binary which does
//! exactly what a lemon binary from lemon.c does, as such, this
//! program is for emitting C code, not Zig code.  This helps me
//! pressure test the port, because a correct program gives
//! identical outputs to the original.
//!
//! From there, the intention is to transform it into `zitron.zig`,
//! which will ultimately be a Zig code generator and use idiomatic
//! Zig (lemon.zig will be fairly C flavored by comparison).
//!

const std = @import("std");
const builtin = @import("builtin");
const Allocator = std.mem.Allocator;
const ArrayHashMap = std.ArrayHashMapUnmanaged;
const MemoryPool = std.heap.MemoryPool;
const ArrayList = std.ArrayListUnmanaged;
const StringArrayHashMap = std.StringArrayHashMapUnmanaged;

const isLower = std.ascii.isLower;
const isUpper = std.ascii.isUpper;
const isAlnum = std.ascii.isAlphanumeric;
const isAlpha = std.ascii.isAlphabetic;
const isSpace = std.ascii.isWhitespace;

const sort = std.mem.sort;

const assert = std.debug.assert;

const exit = std.process.exit;

const logger = std.log.scoped(.lemon);

fn dbgassert(ok: bool) void {
    if (builtin.mode == .Debug) {
        assert(ok);
    }
}

const dprint = std.debug.print;

//| NOTE: this should become a build flag

const lemon_classic = true;

// Various print control variables

/// The main print control for lemon v. lemon comparison
const p_check = true;

const p_print = false;
const p_errcnt = true;
const p_symbols = false;

// NOTE: This is not, in fact, how strcmp works.  If it turns out
// I need anything other than != 0 and == 0 from strcmp, which I doubt,
// I can decide how to handle that then.

fn strcmp(a: []const u8, b: []const u8) bool {
    return std.mem.eql(u8, a, b);
}

inline fn cast(T: type, val: anytype) T {
    return @as(T, @intCast(val));
}

// Definition of `int`.  This should help me figure out which should
// be unsigned, optional, or both, and which should in fact be an
// i32 (if any).  All type references to `int` should disappear.

const int = i32;

// Set low to exercise exception code
const MAXRHS = if (builtin.is_test) 5 else 1000;

threadlocal var showPrecendenceConflict: bool = false;

// Rules of thumb: Capitalize types, convert truthy ints to bool,
// and otherwise stick to the original types and names insofar as
// possible.  `char *` becomes `[]u8`, some of these can be const
// but it's not clear which.
//
// Some other changes are worth making on the fly, but they have to
// be mechanical enough that I can refer to the mutation automatically
// later when I have to use the thing.
//
// A lot of code which should be methods will get translated where it
// lays, as it were.  Moving that stuff inside the type containers will
// happen early though.

//| Line Notes: References to the original file will look like this:
//|
//| [1-20]

//| [1-193] These are forward declarations and custom string handling
//|   stuff, neither of which I expect to need.

//| [194-202] Options.  Here we start translating from C to Zig, both
//|   literally, and in terms of style.  Policy for enums: the type is
//|   PascalCased, the prefix (OPT_ in this case) is dropped, and the
//|   remainder is left alone.  This means often cramped C-isms, such
//|   as "dbl" below, but these are easy to refactor after the fact,
//|   and it's easier to use the same literal terms as the source code.

const OptionType = enum(u8) {
    flag = 1,
    int,
    dbl,
    str,
    fflag,
    fint,
    fdbl,
    fstr,
};

// Fortunately Zig has a mechanism for handling the fact that it has
// keywords which C lacks.  I will de-Magyar the code at some later
// point.

const S_Options = struct {
    type: OptionType,
    label: []const u8,
    arg: []u8,
    message: []const u8,
};

//| [203-238] More forward declarations

//| [239] This defines `LEMON_FALSE` and `LEMON_TRUE` as `Boolean`.  That,
//|   we can fairly skip.

//| [241-430] Fundamental data types

const SymbolType = enum {
    terminal,
    nonterminal,
    multiterminal,
};

const E_Assoc = enum {
    left,
    right,
    none,
    unk, // aka `unknown`
};

/// Symbols (terminals and nonterminals) of the grammar are stored in the following:
const Symbol = struct {
    /// Name of the symbol
    name: []const u8,
    /// Index number for this symbol
    index: u32,
    /// Symbols are all either terminal or nonterminal
    type: SymbolType = .terminal,
    /// Linked list of rules of this (if an NT)
    rule: ?*Rule,
    /// fallback token in case this token doesn't parse
    fallback: ?*Symbol,
    /// Precedence if defined (`null` otherwise)
    prec: ?u16 = null,
    /// Associativity if precedence is defined
    assoc: E_Assoc = .unk,
    /// First-set for all rules of this symbol
    firstset: []bool,
    /// True if NT and can generate an empty string
    lambda: bool,
    /// Number of times used
    usecnt: int,
    /// Code which executes whenever this symbol is
    /// popped from the stack during error processing
    destructor: []u8,
    /// Line number for start of destructor.  Set to
    /// -1 for duplicate destructors.
    destLineno: ?u32,
    /// The data type of information held by this
    /// object. Only used if type==NONTERMINAL
    datatype: []u8,
    /// The data type number.  In the parser, the value
    /// stack is a union.  The .yy%d element of this
    /// union is the correct data type for this object.
    dtnum: int, // No idea what the above means yet ¯\_(ツ)_/¯
    /// True if this symbol ever carries content - if
    /// it is ever more than just syntax
    bContent: bool,
    // following fields are used by MULTITERMINALs only

    /// Number of constituent symbols in the MULTI
    nsubsym: usize, // TODO: Probably redundant with this slice:
    //
    /// Array (slice) of constituent symbols
    subsym: []*Symbol,

    pub const empty: Symbol = .{
        .name = "",
        .index = 0,
        .type = .nonterminal,
        .rule = null,
        .fallback = null,
        .prec = null,
        .assoc = .unk,
        .lambda = false,
        .firstset = undefined,
        .usecnt = 0,
        .destructor = undefined,
        .destLineno = null,
        .datatype = undefined,
        .dtnum = 0,
        .bContent = false,
        .nsubsym = 0,
        .subsym = undefined,
    };

    // Valid, if dodgy, mutable Symbol pointer target:
    pub var start: Symbol = start: {
        var starter: Symbol = .empty;
        starter.name = "!!!Invalid";
        break :start starter;
    };

    pub fn create(allocator: Allocator, name: []const u8) !*Symbol {
        const sp = try allocator.create(Symbol);
        errdefer allocator.destroy(sp);
        sp.* = .empty;
        //| [5446]
        sp.name = name;
        dbgassert(sp.name.len > 0);
        if (isUpper(name[0])) {
            sp.type = .terminal;
        }
        // These do return a pointer, conceivably that can fail?
        sp.firstset = try allocator.alloc(bool, 0);
        errdefer allocator.free(sp.firstset);
        sp.destructor = try allocator.alloc(u8, 0);
        errdefer allocator.free(sp.destructor);
        sp.datatype = try allocator.alloc(u8, 0);
        errdefer allocator.free(sp.datatype);
        sp.subsym = try allocator.alloc(*Symbol, 0);
        errdefer allocator.free(sp.subsym);
        return sp;
    }

    pub fn destroy(sp: *Symbol, allocator: Allocator) void {
        allocator.free(sp.firstset);
        allocator.free(sp.destructor);
        allocator.free(sp.datatype);
        allocator.free(sp.subsym);
        allocator.destroy(sp);
    }
};

/// Each production rule in the grammar is stored in the following structure.
const Rule = struct {
    /// Left-hand side of the rule
    lhs: *Symbol,
    /// Alias for the LHS (empty if none)
    lhsalias: []const u8,
    /// True if left-hand side is the start symbol
    lhsStart: bool,
    /// Line number for the rule
    ruleline: usize,
    /// The RHS symbols
    rhs: []*Symbol,
    /// Number of RHS symbols
    nrhs: usize, // NOTE: This should use rule.rhs.len, eventually.

    /// An alias for each RHS symbol (empty if none)
    rhsalias: [][]const u8,
    /// Line number at which code begins
    line: usize,
    /// The code executed when this rule is reduced
    code: []const u8,
    /// Setup code before code[] above
    codePrefix: []const u8,
    /// Breakdown code after code[] above
    codeSuffix: []const u8,
    /// Precedence symbol for this rule
    precsym: ?*Symbol,
    /// An index number for this rule
    index: u32,
    /// Rule number as used in the generated tables
    iRule: u32,
    /// True if this rule has no associated C code
    noCode: bool,
    /// True if the code has been emitted already
    codeEmitted: bool,
    /// True if this rule is ever reduced
    canReduce: bool,
    /// Reduce actions occur after optimization
    doesReduce: bool,
    /// Reduce is theoretically possible, but prevented
    /// by actions or other outside implementation
    neverReduce: bool,
    /// Next rule with the same LHS
    nextlhs: ?*Rule,
    /// Next rule in the global list
    next: ?*Rule,

    pub const empty = std.mem.zeroInit(Rule, .{ .lhs = undefined });

    pub fn create(allocator: Allocator) !*Rule {
        const rp = try allocator.create(Rule);
        rp.* = .empty;
        return rp;
    }

    pub fn destroy(rp: *Rule, allocator: Allocator) void {
        allocator.free(rp.rhs);
        allocator.free(rp.rhsalias);
        allocator.destroy(rp);
    }
};

const ConfigStatus = enum {
    complete,
    incomplete,
};

// A configuration is a production rule of the grammar together with
// a mark (dot) showing how much of that rule has been processed so far.
// Configurations also contain a follow-set which is a list of terminal
// symbols which are allowed to immediately follow the end of the rule.
// Every configuration is recorded as an instance of the following:

const Config = struct {
    /// The rule upon which the configuration is based
    rp: *Rule,
    /// The parse point
    dot: u32,
    /// Follow-set for this configuration only
    fws: []bool,
    /// Follow-set forward propagation links
    fplp: ?*PLink,
    /// Follow-set backwards propagation links
    bplp: ?*PLink,
    /// Pointer to state which contains this
    stp: ?*State,
    /// used during followset and shift computations
    status: ConfigStatus,
    /// Next configuration in the state
    next: ?*Config,
    /// The next basis configuration
    bp: ?*Config,

    pub const empty: Config = .{
        .rp = undefined,
        .dot = 0,
        .fws = &.{},
        .fplp = null,
        .bplp = null,
        .stp = null, // ??
        .status = .incomplete,
        .next = null,
        .bp = null,
    };
};

const E_Action = enum(u4) {
    shift,
    accept,
    reduce,
    @"error",
    /// A shift/shift conflict
    ssconflict,
    /// Was a reduce, but part of a conflict
    srconflict,
    /// Was a reduce, but part of a conflict
    rrconflict,
    /// Was a shift.  Precedence resolved conflict
    sh_resolved,
    /// Was reduce.  Precedence resolved conflict
    rd_resolved,
    /// Deleted by compression
    not_used,
    /// Shift first, then reduce
    shiftreduce,
    /// Was not initialized (sanity check)
    _not_initialized,
};

/// NOTE: This union is deduc'ed from the code at [3380]
const ActUnion = union(E_Action) {
    shift: *State,
    accept,
    reduce: *Rule,
    @"error",
    ssconflict: *State,
    srconflict: *Rule,
    rrconflict: *Rule,
    sh_resolved: *State,
    rd_resolved: *Rule,
    not_used,
    shiftreduce: *Rule,
    _not_initialized,
};

const ActionAllocator = MemoryPool(Action);
threadlocal var action_allocator: ActionAllocator = undefined; // init in main
threadlocal var action_age: usize = 0;

/// Every shift or reduce operation is stored as one of the following
const Action = struct {
    /// The look-ahead symbol
    sp: *Symbol = undefined,
    x: ActUnion = ._not_initialized,
    /// SHIFTREDUCE optimization to this symbol
    spOpt: ?*Symbol = null,
    /// Next action for this state
    next: ?*Action = null,
    /// Next action with the same hash
    collide: ?*Action = null,
    /// Tie-breaker in sorting
    age: usize,

    // [490]
    pub fn new() !*Action {
        var act = try action_allocator.create();
        act.age = action_age;
        action_age += 1;
        return act;
    }

    //
};

/// Each state of the generated parser's finite state machine
/// is encoded as an instance of the following structure.
const State = struct {
    /// The basis configurations for this state
    bp: *Config = undefined,
    /// All configurations in this set
    cfp: *Config = undefined,
    /// Sequential number for this state
    statenum: u32,
    /// List of actions for this state
    ap: ?*Action,
    /// Number of actions on terminals
    nTknAct: u32,
    /// Number of actions on nonterminals
    nNtAct: u32,
    /// yy_action[] offset for terminals
    iTnkOfst: ?u32,
    /// yy_action[] offset for nonterminals
    iNtOfst: ?u32,
    /// Default action is to REDUCE by this rule
    iDfltReduce: int, // Another ?u32 I think
    /// The default REDUCE rule.
    pDefltReduce: ?*Rule,
    /// True if this is an auto-reduce state
    autoreduce: bool,

    pub const empty: State = .{
        .statenum = 0,
        .ap = null,
        .nTknAct = 0,
        .nNtAct = 0,
        .iTnkOfst = null,
        .iNtOfst = null,
        .iDfltReduce = -1,
        .pDefltReduce = null,
        .autoreduce = false,
    };

    // [541]
    pub fn addAction(st: *State, sym: *Symbol, act_u: ActUnion) void {
        var newaction = Action.new();
        newaction.next = st.ap;
        st.ap = newaction;
        newaction.sp = sym;
        newaction.spOpt = null;
        newaction.x = act_u;
    }
};

const StateContext = struct {
    pub fn hash(_: StateContext, cfp: *Config) u32 {
        var h: u32 = 0;
        var next_cfg: ?*Config = cfp;
        while (next_cfg) |a| {
            h = h * 571 + a.rp.index * 37 + a.dot;
            next_cfg = a.bp;
        }
        return h;
    }

    pub fn eql(_: StateContext, a_cfg: *Config, b_cfg: *Config, _: usize) bool {
        var this_a: ?*Config = a_cfg;
        var this_b: ?*Config = b_cfg;
        while (this_a != null and this_b != null) {
            const a, const b = .{ this_a.?, this_b.? };
            if (a.rp.index != b.rp.index or a.dot != b.dot) {
                return false;
            }
            this_a, this_b = .{ a.next, b.next };
        } else if ((this_a == null and this_b != null) or
            (this_a != null and this_b == null))
        {
            return false;
        }
        return true;
    }
};

//| [5681] State map stuff.

const StateSafe = struct {
    allocator: Allocator,
    safe: ArrayHashMap(*Config, *State, StateContext, true),
};

threadlocal var state_map: StateSafe = undefined;
threadlocal var is_state_map = false;

fn State_init(allocator: Allocator) !void {
    if (is_state_map) return;
    defer is_state_map = true;
    state_map.allocator = allocator;
    state_map.safe = .empty;
    try state_map.safe.ensureTotalCapacity(allocator, 128);
}

fn State_new() !*State {
    const sp = try state_map.allocator.create(State);
    sp.* = .empty;
    return sp;
}

fn State_find(bp: *Config) ?*State {
    dbgassert(is_state_map);
    return state_map.safe.get(bp);
}

fn State_insert(data: *State, key: *Config) !bool {
    dbgassert(is_state_map);
    if (state_map.safe.getKey(key)) |_| return false;
    try state_map.safe.put(state_map.allocator, key, data);
    return true;
}

//| NOTE: These will be sorted, which invalidates the, uh, state,
//| of the state_map.  I think that's ok though.  Tracking what
//| of this data belongs to whom'st will be interesting.
//|

fn State_arrayof() []*State {
    return state_map.safe.values();
}

/// A followset propagation link indicates that the contents of one
/// configuration followset should be propagated to another whenever
/// the first changes.
const PLink = struct {
    /// The configuration to which linked
    cfp: *Config,
    /// The next propagate link
    next: ?*PLink,
};

threadlocal var plink_freelist: MemoryPool(PLink) = undefined;
threadlocal var is_plink_freelist = false;

fn Plink_new() !*PLink {
    dbgassert(is_plink_freelist);
    return try plink_freelist.create();
}

/// Add a plink to a plink list
fn Plink_add(plink: *?*PLink, cfp: *Config) !void {
    const newlink = try Plink_new();
    newlink.cfp = cfp;
    newlink.next = plink.*;
    plink.* = newlink;
}

/// Transfer every plink on the list "from" to the list "to"
fn Plink_copy(to: *?*PLink, from_in: ?*PLink) void {
    var from: ?*PLink = from_in;
    var nextpl: ?*PLink = null;
    while (from) |this_pl| {
        nextpl = this_pl.next;
        this_pl.next = to.*;
        to.* = this_pl;
        from = nextpl;
    }
}

/// Delete every plink on the list
fn Plink_delete(plp_delete: ?*PLink) void {
    var this_plp: ?*PLink = plp_delete;
    while (this_plp) |plp| {
        const plp_next = plp.next;
        plink_freelist.destroy(plp);
        this_plp = plp_next;
    }
}

/// The state vector for the entire parser generator is recorded as
/// follows.  (LEMON uses no global variables and makes little use of
/// static variables.  Fields in the following structure can be thought
/// of as being global variables in the program.)
const Lemon = struct {
    /// Allocator
    allocator: Allocator,
    /// Table of states sorted by state number
    sorted: []*State,
    /// List of all rules
    rule: *Rule,
    /// First rule
    startRule: *Rule,
    /// Number of states
    nstate: u32,
    /// nstate with tail degenerate states removed
    nxstate: u32,
    /// Number of rules
    nrule: u32,
    /// Number of rules with actions
    nruleWithAction: usize,
    /// Number of terminal and nonterminal symbols
    nsymbol: usize,
    /// Number of terminal symbols
    nterminal: usize,
    /// Minimum shift-reduce action value
    minShiftReduce: int,
    /// Error action value
    errAction: int,
    /// Accept action value
    accAction: int,
    /// No-op action value
    noAction: int,
    /// Minimum reduce action
    minReduce: int,
    /// Maximum action value of any kind
    maxAction: int,
    /// Sorted array of pointers to symbols
    symbols: []*Symbol,
    /// Number of errors
    errorcnt: usize,
    /// The error symbol
    errsym: ?*Symbol,
    ///  Token that matches anything
    wildcard: ?*Symbol,
    /// Name of the generated parser
    name: []u8,
    /// Declaration of the 3rd argument to parser
    arg: []u8,
    /// Declaration of 2nd argument to constructor
    ctx: []u8,
    /// Type of terminal symbols in the parser stack
    tokentype: []u8,
    /// The default type of non-terminal symbols
    vartype: []u8,
    /// Name of the start symbol for the grammar
    start: []u8,
    /// Size of the parser stack
    stacksize: []u8,
    /// Code to put at the start of the C file
    include: []u8,
    /// Code to execute when an error is seen
    @"error": []u8,
    /// Code to execute on a stack overflow
    overflow: []u8,
    /// Code to execute on parser failure
    failure: []u8,
    /// Code to execute when the parser excepts
    accept: []u8,
    /// Code appended to the generated file
    extracode: []u8,
    /// Code to execute to destroy token data
    tokendest: []u8,
    /// Code for the default non-terminal destructor
    vardest: []u8,
    /// Name of the input file
    filename: []const u8,
    /// Name of the current output file
    outname: []u8,
    /// A prefix added to token names in the .h file
    tokenprefix: []u8,
    /// Function to use to allocate stack space
    reallocFunc: []u8,
    /// Function to use to free stack space
    freeFunc: []u8,
    nconflict: int,
    nactiontab: int,
    nlookaheadtab: int,
    tablesize: int,
    basisflag: bool,
    printPreprocessed: bool,
    has_fallback: bool,
    nolineosflag: bool,
    argv: [][:0]u8,

    // TODO: we leave several things undefined here which are not
    // guaranteed to be defined in the presence of bad inputs.
    // This can be fixed by making dummy rules which point to
    // dummy symbols, as threadlocal vars (but these we keep).
    // --
    // It is admittedly more convenient to have pointers be always
    // nullable, when it comes to this kind of thing.  Although
    // really this problem is created by that semantic more than it
    // is solved by it, since in Zig we would take more pains while
    // writing code like this to point at valid data as soon as we
    // meaningfully can.

    pub const empty: Lemon = .{
        .allocator = undefined,
        .sorted = &.{},
        .rule = undefined,
        .startRule = undefined,
        .nstate = 0,
        .nxstate = 0,
        .nrule = 0,
        .nruleWithAction = 0,
        .nsymbol = 0,
        .nterminal = 0,
        .minShiftReduce = 0,
        .errAction = 0,
        .accAction = 0,
        .noAction = 0,
        .minReduce = 0,
        .maxAction = 0,
        .symbols = &.{},
        .errorcnt = 0,
        .errsym = null,
        .wildcard = null,
        .name = &.{},
        .arg = &.{},
        .ctx = &.{},
        .tokentype = &.{},
        .vartype = &.{},
        .start = &.{},
        .stacksize = &.{},
        .include = &.{},
        .@"error" = &.{},
        .overflow = &.{},
        .failure = &.{},
        .accept = &.{},
        .extracode = &.{},
        .tokendest = &.{},
        .vardest = &.{},
        .filename = "",
        .outname = &.{},
        .tokenprefix = &.{},
        .reallocFunc = &.{},
        .freeFunc = &.{},
        .nconflict = 0,
        .nactiontab = 0,
        .nlookaheadtab = 0,
        .tablesize = 0,
        .basisflag = false,
        .printPreprocessed = false,
        .has_fallback = false,
        .nolineosflag = false,
        .argv = &.{},
    };

    pub fn create(allocator: Allocator) !*Lemon {
        const gp = try allocator.create(Lemon);
        errdefer allocator.destroy(gp);
        gp.* = .empty;
        gp.allocator = allocator;
        gp.sorted = try allocator.alloc(*Symbol, 0);
        errdefer allocator.free(gp.sorted);
        gp.name = try allocator.alloc(u8, 0);
        errdefer allocator.free(gp.name);
        gp.arg = try allocator.alloc(u8, 0);
        errdefer allocator.free(gp.arg);
        gp.ctx = try allocator.alloc(u8, 0);
        errdefer allocator.free(gp.ctx);
        gp.tokentype = try allocator.alloc(u8, 0);
        errdefer allocator.free(gp.tokentype);
        gp.vartype = try allocator.alloc(u8, 0);
        errdefer allocator.free(gp.vartype);
        gp.start = try allocator.alloc(u8, 0);
        errdefer allocator.free(gp.start);
        gp.stacksize = try allocator.alloc(u8, 0);
        errdefer allocator.free(gp.stacksize);
        gp.include = try allocator.alloc(u8, 0);
        errdefer allocator.free(gp.include);
        gp.@"error" = try allocator.alloc(u8, 0);
        errdefer allocator.free(gp.@"error");
        gp.overflow = try allocator.alloc(u8, 0);
        errdefer allocator.free(gp.overflow);
        gp.failure = try allocator.alloc(u8, 0);
        errdefer allocator.free(gp.failure);
        gp.accept = try allocator.alloc(u8, 0);
        errdefer allocator.free(gp.accept);
        gp.extracode = try allocator.alloc(u8, 0);
        errdefer allocator.free(gp.extracode);
        gp.tokendest = try allocator.alloc(u8, 0);
        errdefer allocator.free(gp.tokendest);
        gp.vardest = try allocator.alloc(u8, 0);
        errdefer allocator.free(gp.vardest);
        gp.filename = try allocator.alloc(u8, 0);
        errdefer allocator.free(gp.filename);
        gp.outname = try allocator.alloc(u8, 0);
        errdefer allocator.free(gp.outname);
        gp.tokenprefix = try allocator.alloc(u8, 0);
        errdefer allocator.free(gp.tokenprefix);
        gp.reallocFunc = try allocator.alloc(u8, 0);
        errdefer allocator.free(gp.reallocFunc);
        gp.argv = undefined; // populated by std.process.argsAlloc.
        return gp;
    }

    pub fn destroy(gp: *Lemon, allocator: Allocator) void {
        allocator.free(gp.sorted);
        allocator.free(gp.name);
        allocator.free(gp.arg);
        allocator.free(gp.ctx);
        allocator.free(gp.tokentype);
        allocator.free(gp.vartype);
        allocator.free(gp.start);
        allocator.free(gp.stacksize);
        allocator.free(gp.include);
        allocator.free(gp.@"error");
        allocator.free(gp.overflow);
        allocator.free(gp.failure);
        allocator.free(gp.accept);
        allocator.free(gp.extracode);
        allocator.free(gp.tokendest);
        allocator.free(gp.vardest);
        allocator.free(gp.outname);
        allocator.free(gp.tokenprefix);
        allocator.free(gp.reallocFunc);
        allocator.destroy(gp);
    }
};

//| [324] Action stuff

// Some of this got distributed to struct namespaces

//|
//| The state of the yy_action table under construction is an instance of
//| the following structure.
//|
//| The yy_action table maps the pair (state_number, lookahead) into an
//| action_number.  The table is an array of integers pairs.  The state_number
//| determines an initial offset into the yy_action array.  The lookahead
//| value is then added to this initial offset to get an index X into the
//| yy_action array. If the aAction[X].lookahead equals the value of the
//| of the lookahead input, then the value of the action_number output is
//| aAction[X].action.  If the lookaheads do not match then the
//| default action for the state_number is returned.
//|
//| All actions associated with a single state_number are first entered
//| into aLookahead[] using multiple calls to acttab_action().  Then the
//| actions for that single state_number are placed into the aAction[]
//| array with a single call to acttab_insert().  The acttab_insert() call
//| also resets the aLookahead[] array in preparation for the next
//| state number.

/// Value of the lookahead token
/// Action to take on the given lookahead
const LookaheadAction = struct {
    /// Value of the lookahead token
    lookahead: i32,
    /// Action to take on the given lookahead
    action: i32,

    pub const empty: LookaheadAction = .{ .lookahead = -1, .action = -1 };
};

const ActTable = struct {
    allocator: Allocator,
    /// The yyaction[] table under construction
    aAction: ArrayList(LookaheadAction) = .empty,
    /// Number of aAction slots in actual use
    nAction: usize = 0,
    /// A single new transaction set
    aLookahead: ArrayList(LookaheadAction) = .empty,
    /// Minimum aLookahead[].lookahead
    mnLookahead: i32 = 0,
    /// Action associated with mnLookahead
    mnAction: i32 = 0,
    /// Maximum aLookahead[].lookahead
    mxLookahead: i32 = 0,
    /// Number of terminal symbols
    nterminal: usize = 0,
    /// total number of symbols
    nsymbol: usize = 0,

    // [541] Action_add
    pub fn create(allocator: Allocator, nsymbol: usize, nterminal: usize) !*ActTable {
        var tab = try allocator.create(ActTable);
        tab.* = .{};
        tab.nsymbol = nsymbol;
        tab.nterminal = nterminal;
        tab.allocator = allocator;
        return tab;
    }

    pub fn destroy(tab: *ActTable) void {
        tab.aAction.deinit(tab.allocator);
        tab.aLookahead.deinit(tab.allocator);
        tab.allocator.destroy(tab);
    }

    /// Return the number of entries in the yy_action table
    pub inline fn lookaheadSize(x: *const ActTable) usize {
        return x.aAction.items.len;
    }

    /// The value for the N-th entry in yy_action
    pub inline fn yyaction(tab: *const ActTable, n: usize) i32 {
        return tab.aAction.items[n].action;
    }

    /// The value for the N-th entry in yy_lookahead
    pub inline fn yylookahead(tab: *const ActTable, n: usize) i32 {
        return tab.aAction.items[n].lookahead;
    }

    // [639]
    /// Add a new action to the current transaction set.
    ///
    /// This routine is called once for each lookahead for a particular
    /// state.
    pub fn action(tab: *ActTable, lookahead: i32, an_action: i32) !void {
        if (tab.aLookahead.items.len >= tab.aLookahead.capacity) {
            try tab.aLookahead.ensureUnusedCapacity(tab.allocator, 25);
        }
        if (tab.aLookahead.items.len == 0) {
            tab.mxLookahead = lookahead;
            tab.mnLookahead = lookahead;
            tab.mnAction = an_action;
        } else {
            if (tab.mxLookahead < lookahead) tab.mxLookahead = lookahead;
            if (tab.mnLookahead > lookahead) {
                tab.mnLookahead = lookahead;
                tab.mnAction = an_action;
            }
        }
        tab.aLookahead.appendAssumeCapacity(
            tab.allocator,
            .{ .lookahead = lookahead, .action = an_action },
        );
    }

    // [683]
    /// Add the transaction set built up with prior calls to acttab_action()
    /// into the current action table.  Then reset the transaction set back
    /// to an empty set in preparation for a new round of acttab_action() calls.
    ///
    /// Return the offset into the action table of the new transaction.
    ///
    /// If the makeItSafe parameter is true, then the offset is chosen so that
    /// it is impossible to overread the yy_lookaside[] table regardless of
    /// the lookaside token.  This is done for the terminal symbols, as they
    /// come from external inputs and can contain syntax errors.  When makeItSafe
    /// is false, there is more flexibility in selecting offsets, resulting in
    /// a smaller table.  For non-terminal symbols, which are never syntax errors,
    /// makeItSafe can be false.
    ///
    pub fn insert(p: *ActTable, makeItSafe: bool) !i32 {
        //  Make sure we have enough space to hold the expanded action table
        // in the worst case.  The worst case occurs if the transaction set
        // must be appended to the current action table.
        assert(p.aLookahead.items.len > 0);
        {
            const n = p.nsymbol + 1;
            if (p.nAction + n >= p.aAction.items.len) {
                // TODO: This value is probably excessive.
                const new_cap = p.nAction + p.aAction.items.len + 20;
                const new_slice = try p.aAction.addManyAsSlice(p.allocator, new_cap);
                @memset(new_slice, LookaheadAction.empty);
            }
        }
        const end = if (makeItSafe) p.mnLookahead else 0;
        // Since we're done allocating, these pointers are stable:
        const act_items = p.aAction.items;
        const look_items = p.aLookahead.items;
        var ii: isize = p.nAction - 1;
        i_loop: while (ii >= end) : (ii -= 1) {
            const i: usize = @intCast(ii);
            if (act_items[i].lookahead == p.mnLookahead) {
                // All lookaheads and actions in the aLookahead[] transaction
                // must match against the candidate aAction[i] entry.
                if (act_items[i].action != p.mnAction) continue :i_loop;
                var j: usize = 0;
                j_loop: while (j < look_items.len) : (j += 1) {
                    const k = look_items[j].lookahead - p.mnLookahead + i;
                    if (k < 0 or k > p.nAction) break :j_loop;
                    if (look_items[j].lookahead != act_items[k].lookahead) break :j_loop;
                    if (look_items[j].action != act_items[k].action) break :j_loop;
                }
                if (j < look_items.len) continue :i_loop;

                // No possible lookahead value that is not in the aLookahead[]
                // transaction is allowed to match aAction[i]
                var n: i32 = 0;
                j = 0;
                j_check: while (j < p.nAction) : (j += 1) {
                    if (act_items[j].lookahead < 0) continue :j_check;
                    if (act_items[j].lookahead == j + p.mnLookahead + i) n += 1;
                }

                if (n == look_items.len) {
                    break :i_loop; //An exact match is found at offset i
                }
            }
        }
        // If no existing offsets exactly match the current transaction, find an
        // an empty offset in the aAction[] table in which we can add the
        // aLookahead[] transaction.
        if (ii < end) {
            // Look for holes in the aAction[] table that fit the current
            // aLookahead[] transaction.  Leave i set to the offset of the hole.
            // If no holes are found, i is left at p->nAction, which means the
            // transaction will be appended.
            var i: usize = if (makeItSafe) @intCast(p.mnLookahead) else 0; // Isn't this 'end'? -Sam
            i_loop: while (i < act_items.len - p.mxLookahead) : (i += 1) {
                if (act_items[i].lookahead < 0) {
                    var j: usize = 0;
                    j_loop: while (j < look_items.len) : (j += 1) {
                        const k = look_items[i].lookahead - p.mxLookahead + i;
                        if (k < 0) break :j_loop;
                        if (act_items[k].lookahead >= 0) break :j_loop;
                    }
                    if (j < look_items.len) continue :i_loop;
                    j = 0;
                    j_check: while (j < act_items.len) : (j += 1) {
                        if (act_items[j].lookahead == j + p.mnLookahead - i) break :j_check;
                    }
                    if (j == act_items.len) {
                        break :i_loop; // Fits in empty slots
                    }
                }
            }
        }
        // Insert transaction set at index i.
        for (0..look_items.len) |j| {
            const k = look_items[j] - p.mnLookahead + ii;
            act_items[cast(usize, k)] = look_items[j];
            if (k > p.nAction) p.nAction = k + 1;
        }

        if (makeItSafe and ii + p.nterminal >= p.nAction) p.nAction = ii + p.nterminal + 1;

        p.aLookahead.clearRetainingCapacity();

        // Return the offset that is added to the lookahead in order to get the
        // index into yy_action of the action
        return ii - p.mnLookahead;
    }

    // [792]
    /// Return the size of the action table without the trailing syntax error entries.
    pub fn actionSize(acttab: *ActTable) usize {
        var n = acttab.nAction;
        while (n > 0 and acttab.aAction.items[n].lookahead < 0) : (n -= 1) {}
        return n;
    }
};

// [803]
///
/// Find a precedence symbol of every rule in the grammar.
///
/// Those rules which have a precedence symbol coded in the input
/// grammar using the "[symbol]" construct will already have the
/// rp->precsym field filled.  Other rules take as their precedence
/// symbol the first RHS symbol with a defined precedence.  If there
/// are not RHS symbols with a defined precedence, the precedence
/// symbol field is left blank.
fn FindRulePrecedences(lem: *Lemon) void {
    var maybe_rp: ?*Rule = lem.rule;
    while (maybe_rp) |rp| : (maybe_rp = rp.next) {
        if (rp.precsym == null) {
            var i: usize = 0;
            while (i < rp.nrhs and rp.precsym == null) : (i += 1) {
                const sp: *Symbol = rp.rhs[i];
                if (sp.type == .multiterminal) {
                    var j: usize = 0;
                    j_loop: while (j < sp.nsubsym) : (j += 1) {
                        if (sp.subsym[j].prec) |_| {
                            rp.precsym = sp.subsym[j];
                            break :j_loop;
                        }
                    }
                } else if (sp.prec) |_| {
                    rp.precsym = rp.rhs[i];
                }
            }
        }
    }
}

// [842]
/// Find all nonterminals which will generate the empty string.
/// Then go back and compute the first sets of every nonterminal.
/// The first set is the set of all terminal symbols which can begin
/// a string generated by that nonterminal.
fn FindFirstSets(lemp: *Lemon) !void {
    for (lemp.symbols) |sym| {
        dbgassert(sym.lambda == false);
    }
    for (lemp.nterminal..lemp.nsymbol) |i| {
        const sym = lemp.symbols[i];
        dbgassert(sym.type == .nonterminal);
        sym.firstset = try lemp.allocator.alloc(bool, set_size);
    }
    // First compute all lambdas
    var progress: bool = true;
    while (progress) {
        progress = false;
        var rp: ?*Rule = lemp.rule;
        walk: while (rp) |rule| : (rp = rule.next) {
            if (rule.lhs.lambda) continue :walk;
            var i: usize = 0;
            sym: while (i < rule.nrhs) : (i += 1) { // TODO: just rule.rhs yeah
                const sp = rule.rhs[i];
                dbgassert(sp.type == .nonterminal or sp.lambda == false);
                if (sp.lambda == false) break :sym;
            } // A rule with no nrhs, or, all lambda, is lambda.
            if (i == rule.nrhs) {
                rule.lhs.lambda = true;
                progress = true;
            }
        }
    }

    // Now compute all first sets
    progress = true;
    while (progress) {
        progress = false;
        var rp: ?*Rule = lemp.rule;
        while (rp) |rule| : (rp = rule.next) {
            const s1 = rule.lhs;
            rhs: for (rule.rhs) |s2| {
                if (s2.type == .terminal) {
                    const p = SetAdd(s1.firstset, s2.index);
                    progress = progress or p;
                    break :rhs;
                } else if (s2.type == .multiterminal) {
                    for (s2.subsym) |ss2| {
                        const p = SetAdd(s1.firstset, ss2.index);
                        progress = progress or p;
                    }
                    break :rhs;
                } else if (s1 == s2) {
                    if (s1.lambda == false) break :rhs;
                } else {
                    const p = SetUnion(s1.firstset, s2.firstset);
                    progress = progress or p;
                    if (s2.lambda == false) break :rhs;
                }
            }
        }
    }
}

// [900]
//
// Compute all LR(0) states for the grammar.  Links
// are added to between some states so that the LR(1) follow sets
// can be computed later.
//
fn FindStates(lemp: *Lemon) !void {
    const sp: *Symbol = sp: {
        if (lemp.start.len > 0) {
            const maybe_sp = Symbol_find(lemp.start);
            if (maybe_sp) |_| {
                break :sp lemp.startRule.lhs;
            } else {
                ErrorMsg(lemp.filename, 0, "" ++
                    "The specified start symbol \"{s}\" is not " ++
                    "in a nonterminal of the grammar.  \"{s}\" will be used as the start " ++
                    "symbol instead.", .{ lemp.start, lemp.startRule.lhs.name });
                lemp.errorcnt += 1;
                break :sp lemp.startRule.lhs;
            }
        } else {
            // OG checks if startRule pointer is defined, we (and it) ensure
            // that it is before we get here.
            break :sp lemp.startRule.lhs;
        }
    };
    // Make sure the start symbol doesn't occur on the right-hand side of
    // any rule.  Report an error if it does.  (YACC would generate a new
    // start symbol in this case.)
    var rp: ?*Rule = lemp.rule;
    while (rp) |rule| : (rp = rule.next) {
        for (rule.rhs) |rhs| {
            if (rhs == sp) {
                ErrorMsg(lemp.filename, 0, "" ++
                    "The start symbol \"{s}\" occurs on the " ++
                    "right-hand side of a rule. This will result in a parser which " ++
                    "does not work properly.", .{sp.name});
                lemp.errorcnt += 1;
            }
            //| NOTE: the previous comparison says FIX ME:  Deal with multiterminals.
            //| I think this is the fix, but we leave it out of lemon classic because
            //| I aim to be mostly bug-compatible.  It's not actually clear this condition
            //| can be triggered in any case.
            if (!lemon_classic) if (rhs.type == .multiterminal) {
                for (rhs.subsym) |subsym| {
                    if (subsym == sp) {
                        ErrorMsg(lemp.filename, 0, "" ++
                            "The start symbol {s} appears as a terminal in a multiterminal. " ++
                            "This was thought to be impossible.", .{sp.name});
                        lemp.errorcnt += 1;
                    }
                }
            };
        }
    }
    // The basis configuration set for the first state
    // is all rules which have the start symbol as their
    // left-hand side.
    rp = sp.rule;
    while (rp) |rule| : (rp = rule.nextlhs) {
        rule.lhsStart = true;
        const new_cfp = try Configlist_addbasis(rule, 0);
        _ = SetAdd(new_cfp.fws, 0);
    }

    // Compute the first state.  All other states will be
    // computed automatically during the computation of the first one.
    // The returned pointer to the first state is not used.
    _ = try getstate(lemp);
}

// [967]
// Return a pointer to a state which is described by the configuration
// list which has been built from calls to Configlist_add.
fn getstate(lemp: *Lemon) !*State {
    // Extract the sorted basis of the new state.  The basis was constructed
    // by prior calls to "Configlist_addbasis()".
    Configlist_sortbasis();
    const maybe_bp = Configlist_basis();
    const maybe_stp = if (maybe_bp) |bp| State_find(bp) else null;
    if (maybe_stp) |stp| {
        // A state with the same basis already exists!  Copy all the follow-set
        // propagation links from the state under construction into the
        // preexisting state, then return a pointer to the preexisting state
        var maybe_x: ?*Config = maybe_bp;
        var maybe_y: ?*Config = stp.bp;
        while (maybe_x) |x| while (maybe_y) |y| : ({
            maybe_x = x.bp;
            maybe_y = y.bp;
        }) {
            Plink_copy(&y.bplp, x.bplp);
            Plink_delete(x.fplp);
            x.fplp = null;
            y.fplp = null;
        };
        Configlist_eat(Configlist_return(), lemp.allocator);
        return stp;
    } else {
        // This really is a new state.  Construct all the details
        try Configlist_closure(lemp);
        Configlist_sort();
        const cfp = Configlist_return().?;
        const stp = try State_new();
        stp.bp = maybe_bp.?;
        stp.cfp = cfp;
        stp.statenum = lemp.nstate;
        lemp.nstate += 1;
        stp.ap = null;
        _ = try State_insert(stp, stp.bp);
        // try  buildshifts(lemp, stp);
        return stp;
    }
}

fn buildshifts(lemp: *Lemon, stp: *State) !void {
    _ = .{ lemp, stp };
}

//| [1500] ErrorMsg

fn ErrorMsg(filename: []const u8, lineno: usize, comptime fmt: []const u8, args: anytype) void {
    std.debug.print("{s}:{d}: ", .{ filename, lineno });
    std.debug.print(fmt, args);
    std.debug.print("{s}", .{"\n"});
}

//| [2211] From parse.c

/// The state of the parser
const E_State = enum {
    initialize,
    waiting_for_decl_or_rule,
    waiting_for_decl_keyword,
    waiting_for_decl_arg,
    waiting_for_precedence_symbol,
    waiting_for_arrow,
    in_rhs,
    lhs_alias_1,
    lhs_alias_2,
    lhs_alias_3,
    rhs_alias_1,
    rhs_alias_2,
    precedence_mark_1,
    precedence_mark_2,
    resync_after_rule_error,
    resync_after_decl_error,
    waiting_for_destructor_symbol,
    waiting_for_datatype_symbol,
    waiting_for_fallback_id,
    waiting_for_wildcard_id,
    waiting_for_class_id,
    waiting_for_class_token,
    waiting_for_token_name,
};

pub const PState = struct {
    allocator: Allocator,
    /// Name of the input file
    filename: []const u8,
    /// Line number at which current token starts
    tokenlineno: usize,
    /// Number of errors so far
    errorcnt: usize,
    /// Start index of current token
    tokenstart: usize,
    /// Global state vector
    gp: *Lemon,
    /// The state of the parser
    state: E_State,
    /// The fallback token
    fallback: ?*Symbol,
    /// Token class symbol
    tkclass: *Symbol,
    /// Left-hand side of current rule
    lhs: *Symbol,
    /// Alias for the LHS
    lhsalias: []const u8,
    /// Number of right-hand side symbols seen
    nrhs: usize, // TODO: rhs.len right?
    /// RHS symbols
    rhs: []*Symbol,
    /// Aliases for each RHS symbol (or null)
    alias: [][]const u8, // We'll use empty slices as per usual
    /// Previous rule parsed
    prevrule: ?*Rule,
    /// Keyword of a declaration
    declkeyword: []const u8,
    /// Where the declaration argument should be put
    declargslot: ?*[]u8,
    /// Add `#line` before declaration insert
    insertLineMacro: bool,
    /// Where to write declaration line number
    decllinenoslot: ?*?u32, // The destination on Symbol is itself nullable.
    /// Assign this association to decl arguments
    declassoc: E_Assoc,
    /// Assign this precedence to decl arguments
    preccounter: u16,
    /// Pointer to first rule in the grammar
    firstrule: ?*Rule,
    /// Pointer to the most recently parsed rule
    lastrule: ?*Rule,

    pub const empty: PState = .{
        .allocator = undefined,
        .filename = "",
        .tokenlineno = 0,
        .tokenstart = 0,
        .errorcnt = 0,
        .gp = undefined,
        .state = .initialize,
        .fallback = null,
        .tkclass = &Symbol.start,
        .lhs = &Symbol.start,
        .lhsalias = "",
        .nrhs = 0,
        .rhs = &.{},
        .alias = &.{},
        .prevrule = null,
        .declkeyword = "",
        .declargslot = null,
        .insertLineMacro = false,
        .decllinenoslot = null,
        .declassoc = .unk,
        .preccounter = 0,
        .firstrule = null,
        .lastrule = null,
    };

    pub fn create(allocator: Allocator, gp: *Lemon) !*PState {
        var psp = try allocator.create(PState);
        errdefer allocator.destroy(psp);
        psp.* = .empty;
        psp.allocator = allocator;
        psp.gp = gp;
        psp.rhs = try allocator.alloc(*Symbol, MAXRHS);
        errdefer allocator.free(psp.rhs);
        psp.alias = try allocator.alloc([]const u8, MAXRHS);
        errdefer allocator.free(psp.alias);
        return psp;
    }

    // No clue how to dispose of things yet. But I think the answer is that Symbols all
    // live in the intern pool, with the strings, and we just nuke 'em at the end.
    // So...
    pub fn destroy(ps: *PState) void {
        ps.allocator.free(ps.rhs);
        ps.allocator.free(ps.alias);
        var rule_p = ps.firstrule;
        while (rule_p) |r| {
            const next = r.next;
            r.destroy(ps.allocator);
            rule_p = next;
        }
        ps.allocator.destroy(ps);
    }
};

// TODO: move the file stuff here, and use a stack psp like the OG
fn Parse(psp: *PState) !void {
    const file = if (std.fs.cwd().openFile(psp.filename, .{})) |f| file: {
        break :file f;
    } else |err| {
        // TODO: nicer message here
        std.debug.print("File open error {s}", .{@errorName(err)});
        exit(@truncate(@intFromError(err)));
    };
    defer file.close();
    const end_pos = try file.getEndPos();
    const filebuf = try psp.allocator.allocSentinel(u8, end_pos, 0);
    defer psp.allocator.free(filebuf);
    const read_bytes = try file.readAll(filebuf);
    if (read_bytes < end_pos) {
        std.debug.print("didnt read to end of file {s}\n", .{psp.filename});
        std.process.exit(1);
    }
    // /* Make an initial pass through the file to handle %ifdef and %ifndef */
    // preprocess_input(filebuf);
    // if( gp->printPreprocessed ){
    //   printf("%s\n", filebuf);
    //   return;
    // }
    //
    try scan(psp, filebuf);
    if (psp.gp.nrule > 0) {
        psp.gp.rule = psp.firstrule.?;
    }
    psp.gp.errorcnt = psp.errorcnt;
}

fn parseonetoken(psp: *PState, x_init: []const u8) !void {
    const x = try Strsafe(x_init);
    // This seems to be presumed (?)
    assert(x.len != 0);
    if (p_print) std.debug.print("state: {s}  ", .{@tagName(psp.state)});
    if (p_print) if (x.len < 50) {
        std.debug.print("token: {s}\n", .{x});
    } else {
        std.debug.print("token: {s}...\n", .{x[0..50]});
    };
    if (p_errcnt) if (psp.gp.errorcnt > 0) {
        std.debug.print("error count: {d}\n", .{psp.gp.errorcnt});
    };
    state: switch (psp.state) {
        .initialize => { // TODO: Probably just do this first yeah
            psp.prevrule = null;
            psp.preccounter = 0;
            psp.firstrule, psp.lastrule = .{ null, null };
            psp.gp.nrule = 0;
            continue :state .waiting_for_decl_or_rule;
        },
        .waiting_for_decl_or_rule => {
            if (x[0] == '%') {
                psp.state = .waiting_for_decl_keyword;
            } else if (isLower(x[0])) {
                psp.lhs = try Symbol_new(x);
                psp.nrhs = 0;
                psp.lhsalias = "";
                psp.state = .waiting_for_arrow;
            } else if (x[0] == '{') {
                if (psp.prevrule) |prev| {
                    if (prev.code.len != 0) {
                        ErrorMsg(psp.filename, psp.tokenlineno, "" ++
                            "Code fragment beginning on this line is not the first " ++
                            "to follow the previous rule.", .{});
                        psp.errorcnt += 1;
                    } else if (strcmp(x, "{NEVER-REDUCE")) {
                        // Hidden feature!
                        prev.neverReduce = true;
                    } else {
                        prev.line = psp.tokenlineno;
                        prev.code = x[1..]; // Code lacks outer braces
                        prev.noCode = false;
                    }
                } else {
                    ErrorMsg(psp.filename, psp.tokenlineno, "" ++
                        "There is no prior rule upon which to attach the code " ++
                        "fragment which begins on this line", .{});
                    psp.errorcnt += 1;
                }
            } else if (x[0] == '[') {
                psp.state = .precedence_mark_1;
            } else {
                ErrorMsg(psp.filename, psp.tokenlineno, "" ++
                    "Token {s} should be either \"%\" or a nonterminal name.", .{x});
                psp.errorcnt += 1;
            }
        },
        .precedence_mark_1 => {
            if (!isUpper(x[0])) {
                ErrorMsg(psp.filename, psp.tokenlineno, "" ++
                    "The precedence symbol must be a terminal.", .{});
                psp.errorcnt += 1;
            } else if (psp.prevrule) |prev| {
                if (prev.precsym) |_| {
                    ErrorMsg(psp.filename, psp.tokenlineno, "" ++
                        "Precedence mark on this line is not the first " ++
                        "to follow the previous rule.", .{});
                    psp.errorcnt += 1;
                } else {
                    prev.precsym = try Symbol_new(x);
                }
            } else {
                ErrorMsg(psp.filename, psp.tokenlineno, "" ++
                    "There is no prior rule to assign precedence \"{s}\".", .{x});
                psp.errorcnt += 1;
            }
            psp.state = .precedence_mark_2;
        },
        .precedence_mark_2 => {
            if (x[0] != ']') {
                ErrorMsg(psp.filename, psp.tokenlineno, "" ++
                    "Missing \"]\" on precedence mark.", .{});
                psp.errorcnt += 1;
            }
            psp.state = .waiting_for_decl_or_rule;
        },
        .waiting_for_arrow => {
            if (x.len >= 3 and x[0] == ':' and x[1] == ':' and x[2] == '=') {
                psp.state = .in_rhs;
            } else if (x[0] == '(') {
                psp.state = .lhs_alias_1;
            } else {
                ErrorMsg(psp.filename, psp.tokenlineno, "" ++
                    "Expected to see a \":\" following the LHS symbol \"%s\".", .{});
                psp.errorcnt += 1;
                psp.state = .resync_after_rule_error;
            }
        },
        .lhs_alias_1 => {
            if (isAlpha(x[0])) {
                psp.lhsalias = x;
                psp.state = .lhs_alias_2;
            } else {
                ErrorMsg(psp.filename, psp.tokenlineno, "" ++
                    "\"%s\" is not a valid alias for the LHS \"%s\"\n", .{});
                psp.errorcnt += 1;
                psp.state = .resync_after_rule_error;
            }
        },
        .lhs_alias_2 => {
            if (x[0] == ')') {
                psp.state = .lhs_alias_3;
            } else {
                ErrorMsg(psp.filename, psp.tokenlineno, "" ++
                    "Missing \")\" following LHS alias name \"{s}\".", .{psp.lhsalias});
                psp.errorcnt += 1;
                psp.state = .resync_after_rule_error;
            }
        },
        .lhs_alias_3 => {
            if (x.len >= 3 and x[0] == ':' and x[1] == ':' and x[2] == '=') {
                psp.state = .in_rhs;
            } else {
                ErrorMsg(psp.filename, psp.tokenlineno, "" ++
                    "Missing \"::=\" following: \"{s}({s})\".", //
                    .{ psp.lhs.name, psp.lhsalias });
                psp.errorcnt += 1;
                psp.state = .resync_after_rule_error;
            }
        },
        .in_rhs => {
            if (x[0] == '.') {
                // Note that the original code allocates one contiguous block of
                // bytes, doling them out to the three separate allocations below.
                // Not without regret, I am not, at this time, willing to follow suit.
                const rp = try Rule.create(psp.allocator);
                errdefer rp.destroy(psp.allocator);
                rp.ruleline = psp.tokenlineno;
                rp.rhs = try psp.allocator.alloc(*Symbol, psp.nrhs);
                rp.rhsalias = try psp.allocator.alloc([]const u8, psp.nrhs);
                for (0..psp.nrhs) |i| {
                    rp.rhs[i] = psp.rhs[i];
                    rp.rhsalias[i] = psp.alias[i];
                }
                rp.lhs = psp.lhs;
                rp.lhsalias = psp.lhsalias;
                rp.nrhs = psp.nrhs;
                rp.noCode = true; // Can be falsified subsequently..
                rp.index = psp.gp.nrule;
                psp.gp.nrule += 1;
                rp.nextlhs = rp.lhs.rule;
                if (psp.firstrule == null) {
                    psp.firstrule = rp;
                    psp.lastrule = rp;
                } else { // Append to linked list
                    psp.lastrule.?.next = rp;
                    psp.lastrule = rp;
                }
                psp.prevrule = rp;
                psp.state = .waiting_for_decl_or_rule;
            } else if (isAlpha(x[0])) {
                if (psp.nrhs >= MAXRHS) {
                    ErrorMsg(psp.filename, psp.tokenlineno, "" ++
                        "Too many symbols on RHS of rule beginning at \"{s}\".", .{x});
                    psp.errorcnt += 1;
                    psp.state = .resync_after_rule_error;
                } else {
                    psp.rhs[psp.nrhs] = try Symbol_new(x);
                    psp.alias[psp.nrhs] = "";
                    psp.nrhs += 1;
                }
            } else if ((x[0] == '|' or x[0] == '/') and psp.nrhs > 0 and x.len > 0 and isUpper(x[1])) {
                var msp = psp.rhs[psp.nrhs - 1];
                if (msp.type != .multiterminal) {
                    const origmsp = msp;
                    msp = try Symbol.create(psp.allocator, origmsp.name);
                    errdefer msp.destroy(psp.allocator);
                    msp.type = .multiterminal;
                    msp.nsubsym = 1;
                    msp.subsym = try psp.allocator.alloc(*Symbol, 1);
                    msp.subsym[0] = origmsp;
                    psp.rhs[psp.nrhs - 1] = msp;
                    // These go on a separate freelist
                    const fl = try psp.allocator.create(SymFreelist);
                    errdefer comptime unreachable;
                    fl.* = .{
                        .sp = msp,
                        .next = null,
                    };
                    if (sym_freelist) |free| {
                        fl.next = free;
                        sym_freelist = fl;
                    } else {
                        sym_freelist = fl;
                    }
                }
                msp.nsubsym += 1;
                msp.subsym = try psp.allocator.realloc(msp.subsym, msp.subsym.len + 1);
                // We know x[1] exists and is terminal-shaped, so this is valid:
                msp.subsym[msp.nsubsym - 1] = try Symbol_new(x[1..]);
                if (isLower(x[1]) or isLower(msp.subsym[0].name[0])) {
                    ErrorMsg(psp.filename, psp.tokenlineno, "" ++
                        "Cannot form a compound containing a non-terminal", .{});
                    psp.errorcnt += 1;
                    psp.state = .resync_after_rule_error;
                }
            } else if (x[0] == '(' and psp.nrhs > 0) {
                psp.state = .rhs_alias_1;
            } else {
                ErrorMsg(psp.filename, psp.tokenlineno, "" ++
                    "Illegal character on RHS of rule: \"{s}\".", .{x});
                psp.errorcnt += 1;
                psp.state = .resync_after_rule_error;
            }
        },
        .rhs_alias_1 => {
            if (isAlpha(x[0])) {
                psp.alias[psp.nrhs - 1] = x;
                psp.state = .rhs_alias_2;
            } else {
                ErrorMsg(psp.filename, psp.tokenlineno, "" ++
                    "\"{s}\" is not a valid alias for the RHS symbol \"{s}\"\n", //
                    .{ x, psp.rhs[psp.nrhs - 1].name });
                psp.errorcnt += 1;
                psp.state = .resync_after_rule_error;
            }
        },
        .rhs_alias_2 => {
            if (x[0] == ')') {
                psp.state = .in_rhs;
            } else {
                ErrorMsg(psp.filename, psp.tokenlineno, "" ++
                    "Missing \")\" following LHS alias name \"{s}\".", .{x});
                psp.errorcnt += 1;
                psp.state = .resync_after_rule_error;
            }
        },
        .waiting_for_decl_keyword => {
            // This I'm doing with an enum, a StaticStringMap, and a switch.
            const decl = declarations.get(x) orelse {
                if (isAlpha(x[0])) {
                    ErrorMsg(psp.filename, psp.tokenlineno, "" ++
                        "Unknown declaration keyword: \"%{s}\".", .{x});
                } else {
                    ErrorMsg(psp.filename, psp.tokenlineno, "" ++
                        "Illegal declaration keyword: \"%{s}\".", .{x});
                }
                psp.errorcnt += 1;
                psp.state = .resync_after_decl_error;
                break :state;
            };
            // Defaults:
            psp.declkeyword = x;
            psp.declargslot = null;
            psp.decllinenoslot = null;
            psp.insertLineMacro = true;
            psp.state = .waiting_for_decl_arg;
            switch (decl) {
                .name => {
                    psp.declargslot = &psp.gp.name;
                    psp.insertLineMacro = false;
                },
                .include => {
                    psp.declargslot = &psp.gp.include;
                },
                .code => {
                    psp.declargslot = &psp.gp.extracode;
                },
                .token_destructor => {
                    psp.declargslot = &psp.gp.tokendest;
                },
                .default_destructor => {
                    psp.declargslot = &psp.gp.vardest;
                },
                .token_prefix => {
                    psp.declargslot = &psp.gp.tokenprefix;
                    psp.insertLineMacro = false;
                },
                .syntax_error => {
                    psp.declargslot = &psp.gp.@"error";
                },
                .parse_accept => {
                    psp.declargslot = &psp.gp.accept;
                },
                .parse_failure => {
                    psp.declargslot = &psp.gp.failure;
                },
                .stack_overflow => {
                    psp.declargslot = &psp.gp.overflow;
                },
                .extra_argument => {
                    psp.declargslot = &psp.gp.arg;
                    psp.insertLineMacro = false;
                },
                .extra_context => {
                    psp.declargslot = &psp.gp.ctx;
                    psp.insertLineMacro = false;
                },
                .token_type => {
                    psp.declargslot = &psp.gp.tokentype;
                    psp.insertLineMacro = false;
                },
                .default_type => {
                    psp.declargslot = &psp.gp.vartype;
                    psp.insertLineMacro = false;
                },
                .realloc => {
                    psp.declargslot = &psp.gp.reallocFunc;
                    psp.insertLineMacro = false;
                },
                .free => {
                    psp.declargslot = &psp.gp.freeFunc;
                    psp.insertLineMacro = false;
                },
                .stack_size => {
                    psp.declargslot = &psp.gp.stacksize;
                    psp.insertLineMacro = false;
                },
                .start_symbol => {
                    psp.declargslot = &psp.gp.start;
                    psp.insertLineMacro = false;
                },
                .left => {
                    psp.preccounter += 1;
                    psp.declassoc = .left;
                    psp.state = .waiting_for_precedence_symbol;
                },
                .right => {
                    psp.preccounter += 1;
                    psp.declassoc = .right;
                    psp.state = .waiting_for_precedence_symbol;
                },
                .nonassoc => {
                    psp.preccounter += 1;
                    psp.declassoc = .none;
                    psp.state = .waiting_for_precedence_symbol;
                },
                .destructor => {
                    psp.state = .waiting_for_destructor_symbol;
                },
                .type => {
                    psp.state = .waiting_for_datatype_symbol;
                },
                .fallback => {
                    psp.fallback = null;
                    psp.state = .waiting_for_fallback_id;
                },
                .token => {
                    psp.state = .waiting_for_token_name;
                },
                .wildcard => {
                    psp.state = .waiting_for_wildcard_id;
                },
                .token_class => {
                    psp.state = .waiting_for_class_id;
                },
            }
        },
        .waiting_for_destructor_symbol => {
            if (!isAlpha(x[0])) {
                ErrorMsg(psp.filename, psp.tokenlineno, "" ++
                    "Symbol name missing after %destructor keyword", .{});
                psp.errorcnt += 1;
                psp.state = .resync_after_decl_error;
                break :state;
            }
            const sp = try Symbol_new(x);
            psp.declargslot = &sp.destructor;
            psp.decllinenoslot = &sp.destLineno;
            psp.insertLineMacro = true;
            psp.state = .waiting_for_decl_arg;
        },
        .waiting_for_datatype_symbol => {
            if (!isAlpha(x[0])) {
                ErrorMsg(psp.filename, psp.tokenlineno, "" ++
                    "Symbol name missing after %type keyword", .{});
                psp.errorcnt += 1;
                psp.state = .resync_after_decl_error;
                break :state;
            }
            const sp = Symbol_find(x) orelse try Symbol_new(x);
            if (sp.datatype.len != 0) {
                ErrorMsg(psp.filename, psp.tokenlineno, "" ++
                    "Symbol %type \"{s}\" already defined", .{x});
                psp.errorcnt += 1;
                psp.state = .resync_after_decl_error;
            } else {
                psp.declargslot = &sp.datatype;
                psp.insertLineMacro = false;
                psp.state = .waiting_for_decl_arg;
            }
        },
        .waiting_for_precedence_symbol => {
            if (x[0] == '.') {
                psp.state = .waiting_for_decl_or_rule;
            } else if (isUpper(x[0])) {
                const sp = try Symbol_new(x);
                if (sp.prec) |_| {
                    ErrorMsg(psp.filename, psp.tokenlineno, "" ++
                        "Symbol \"{s}\" has already be given a precedence.", .{x});
                    psp.errorcnt += 1;
                    // No new state assigned here (?)
                } else {
                    sp.prec = psp.preccounter;
                    sp.assoc = psp.declassoc;
                }
            } else {
                ErrorMsg(psp.filename, psp.tokenlineno, "" ++
                    "Can't assign a precedence to \"{s}\".", .{x});
                psp.errorcnt += 1;
            }
        },
        .waiting_for_decl_arg => {
            if (x[0] == '{' or x[0] == '"' or isAlnum(x[0])) {
                // NOTE: This is a difficult translation, because we eschew two
                // Cisms: the null sentinel, and (consequently) bare char *. So
                // idiomatic Zig looks quite different.
                var zBuffer: [50]u8 = undefined; // Line macro buffer
                // The code assumes declargslot is pointing at something, so null should be
                // unreachable here:
                const declargslot = psp.declargslot.?;
                const zOld: []const u8 = declargslot.*;
                const zNew = if (x[0] == '"' or x[0] == '{') x[1..] else x;
                var zLine: []u8 = zBuffer[0..0];
                // To build the new slice, we have to track bytes written:
                var zIdx: usize = 0;
                // The original code leaves some buffer here, because C
                // makes it difficult to count sprintf statements.  A problem
                // we do not have.
                var n = zOld.len + zNew.len;
                // Do we need a line macro?
                const addLineMacro = !psp.gp.nolineosflag and
                    psp.insertLineMacro and
                    psp.tokenlineno > 1 and
                    (psp.decllinenoslot == null or psp.decllinenoslot.?.* != 0);
                if (addLineMacro) {
                    var nBack = std.mem.count(u8, psp.filename, "\\");
                    nBack += std.mem.count(u8, psp.filename, "\"");
                    zLine = std.fmt.bufPrint(&zBuffer, "#line {d} ", .{psp.tokenlineno}) catch |err| slice: {
                        // Should be literally impossible but ¯\_(ツ)_/¯
                        ErrorMsg(psp.filename, psp.tokenlineno, "" ++
                            "Buffer overflow on #line directive print: {s}", .{@errorName(err)});
                        psp.errorcnt += 1;
                        break :slice zBuffer[0..0];
                    }; // 3 for ", ", \n:
                    n += zLine.len + psp.filename.len + nBack + 3;
                }
                // We put this back on declargslot and PSP once we know how long the
                // slice actually should be.
                const zBuf = try psp.allocator.realloc(declargslot.*, n);
                @memcpy(zBuf[0..zOld.len], zOld);
                zIdx += zOld.len;
                if (addLineMacro) {
                    // TODO: there's no reason to do this repeatedly for every loop,
                    // the file name is not going to change.  This should be
                    // calculated once on load and the value put on gp, *Lemon.
                    if (zIdx > 0 and zBuf[zIdx - 1] != '\n') {
                        zBuf[zIdx] = '\n';
                        zIdx += 1;
                    }
                    @memcpy(zBuf[zIdx..][0..zLine.len], zLine);
                    zIdx += zLine.len + 1;
                    zBuf[zIdx - 1] = '"';
                    for (0..psp.filename.len) |i| {
                        if (psp.filename[i] == '\\' or psp.filename[i] == '"') {
                            zBuf[zIdx] = '\\';
                            zIdx += 1;
                        }
                        zBuf[zIdx] = psp.filename[i];
                        zIdx += 1;
                    }
                    zBuf[zIdx] = '"';
                    zBuf[zIdx + 1] = '\n';
                    zIdx += 2;
                }
                if (psp.decllinenoslot) |linenoslot| if (linenoslot.* == 0) {
                    psp.decllinenoslot.?.* = @intCast(psp.tokenlineno);
                };
                @memcpy(zBuf[zIdx..][0..zNew.len], zNew);
                zIdx += zNew.len;
                // Finally, we put it all where it's pointed:
                declargslot.* = zBuf;
                dbgassert(zIdx == zBuf.len);
                dbgassert(psp.declargslot == declargslot);
                psp.state = .waiting_for_decl_or_rule;
            } else {
                ErrorMsg(psp.filename, psp.tokenlineno, "" ++
                    "Illegal argument to %{s}: {s}", .{ psp.declkeyword, x });
                psp.errorcnt += 1;
                psp.state = .resync_after_decl_error;
            }
        },
        .waiting_for_fallback_id => {
            if (x[0] == '.') {
                psp.state = .waiting_for_decl_or_rule;
            } else if (!isUpper(x[0])) {
                ErrorMsg(psp.filename, psp.tokenlineno, "" ++
                    "%fallback argument \"{s}\" should be a token", .{x});
                psp.errorcnt += 1;
                // TODO: no resync here, is that right?
            } else {
                const sp = try Symbol_new(x);
                if (psp.fallback == null) {
                    psp.fallback = sp;
                } else if (sp.fallback != null) {
                    ErrorMsg(psp.filename, psp.tokenlineno, "" ++
                        "More than one fallback assigned to token {s}", .{sp.name});
                    psp.errorcnt += 1;
                    // TODO: no resync here, is that right?
                } else {
                    sp.fallback = psp.fallback;
                    psp.gp.has_fallback = true;
                }
            }
        },
        .waiting_for_token_name => {
            // Tokens do not have to be declared before use.  But they can be
            // in order to control their assigned integer number.  The number for
            // each token is assigned when it is first seen.  So by including
            //
            //     %token ONE TWO THREE.
            //
            // early in the grammar file, that assigns small consecutive values
            // to each of the tokens ONE TWO and THREE.
            //
            if (x[0] == '.') {
                psp.state = .waiting_for_decl_or_rule;
            } else if (!isUpper(x[0])) {
                ErrorMsg(psp.filename, psp.tokenlineno, "" ++
                    "%token argument \"{s}\" should be a token", .{x});
                psp.errorcnt += 1;
            } else {
                _ = try Symbol_new(x);
            }
        },
        .waiting_for_wildcard_id => {
            if (x[0] == '.') {
                psp.state = .waiting_for_decl_or_rule;
            } else if (!isUpper(x[0])) {
                ErrorMsg(psp.filename, psp.tokenlineno, "" ++
                    "%wildcard argument \"{s}\" should be a token", .{x});
                psp.errorcnt += 1;
            } else {
                const sp = try Symbol_new(x);
                if (psp.gp.wildcard == null) {
                    psp.gp.wildcard = sp;
                } else {
                    ErrorMsg(psp.filename, psp.tokenlineno, "" ++
                        "Extra wildcard to token: {s}", .{x});
                    psp.errorcnt += 1;
                }
            }
        },
        .waiting_for_class_id => {
            if (!isLower(x[0])) {
                ErrorMsg(psp.filename, psp.tokenlineno, "" ++
                    "%token_class must be followed by an identifier: {s}", .{x});
                psp.errorcnt += 1;
                psp.state = .resync_after_decl_error;
            } else if (Symbol_find(x)) |_| {
                ErrorMsg(psp.filename, psp.tokenlineno, "" ++
                    "Symbol \"{s}\" already used", .{x});
                psp.errorcnt += 1;
                psp.state = .resync_after_decl_error;
            } else {
                psp.tkclass = try Symbol_new(x);
                psp.tkclass.type = .multiterminal;
                psp.state = .waiting_for_class_token;
            }
        },
        .waiting_for_class_token => {
            if (x[0] == '.') {
                psp.state = .waiting_for_decl_or_rule;
            } else if (isUpper(x[0]) or ((x[0] == '|' or x[0] == '/') and isUpper(x[1]))) {
                const msp = psp.tkclass;
                msp.nsubsym += 1;
                msp.subsym = subsym: {
                    if (msp.subsym.len == 0)
                        break :subsym try psp.allocator.alloc(*Symbol, 1)
                    else
                        break :subsym try psp.allocator.realloc(msp.subsym, msp.nsubsym);
                };
                msp.subsym[msp.nsubsym - 1] = try Symbol_new(if (!isUpper(x[0])) x else x[1..]);
            } else {
                ErrorMsg(psp.filename, psp.tokenlineno, "" ++
                    "%token_class argument \"{s}\" should be a token", .{x});
                psp.errorcnt += 1;
                psp.state = .resync_after_decl_error;
            }
        },
        // TODO: These don't need to be separate states
        .resync_after_rule_error,
        .resync_after_decl_error,
        => {
            if (x[0] == '.') psp.state = .waiting_for_decl_or_rule;
            if (x[0] == '%') psp.state = .waiting_for_decl_keyword;
        },
    }
}

const Declaration = enum {
    name,
    include,
    code,
    token_destructor,
    default_destructor,
    token_prefix,
    syntax_error,
    parse_accept,
    parse_failure,
    stack_overflow,
    extra_argument,
    extra_context,
    token_type,
    default_type,
    realloc,
    free,
    stack_size,
    start_symbol,
    left,
    right,
    nonassoc,
    destructor,
    type,
    fallback,
    token,
    wildcard,
    token_class,
};

const directive_list = [_]struct { []const u8, Declaration }{
    .{ "name", .name },
    .{ "include", .include },
    .{ "code", .code },
    .{ "token_destructor", .token_destructor },
    .{ "default_destructor", .default_destructor },
    .{ "token_prefix", .token_prefix },
    .{ "syntax_error", .syntax_error },
    .{ "parse_accept", .parse_accept },
    .{ "parse_failure", .parse_failure },
    .{ "stack_overflow", .stack_overflow },
    .{ "extra_argument", .extra_argument },
    .{ "extra_context", .extra_context },
    .{ "token_type", .token_type },
    .{ "default_type", .default_type },
    .{ "realloc", .realloc },
    .{ "free", .free },
    .{ "stack_size", .stack_size },
    .{ "start_symbol", .start_symbol },
    .{ "left", .left },
    .{ "right", .right },
    .{ "nonassoc", .nonassoc },
    .{ "destructor", .destructor },
    .{ "type", .type },
    .{ "fallback", .fallback },
    .{ "token", .token },
    .{ "wildcard", .wildcard },
    .{ "token_class", .token_class },
};

const declarations = std.StaticStringMap(Declaration).initComptime(directive_list);

/// Lemon puts the scanner loop in `Parse`, I prefer it separate.
fn scan(ps: *PState, fb: [:0]const u8) !void {
    var i: usize = 0;
    var lineno: usize = 1;
    scanning: while (i < fb.len) {
        var skip: bool = false; // True when we advance one more before loop
        if (fb[i] == '\n') lineno += 1;
        if (isSpace(fb[i])) {
            i += 1;
            continue :scanning;
        } // Skip all whitespace
        // Skip C++ style comments
        if (fb[i] == '/' and fb[i + 1] == '/') {
            i += 2;
            while (fb[i] != '\n' and fb[i] != 0) : (i += 1) {}
            if (fb[i] != 0) {
                if (fb[i] == '\n') lineno += 1;
                i += 1;
                continue :scanning;
            } else break :scanning;
        }
        // Skip C style comments
        if (fb[i] == '/' and fb[i + 1] == '*') {
            i += 2;
            if (fb[i] != 0) break :scanning;
            if (fb[i] == '*') i += 1;
            if (fb[i] != 0) break :scanning;
            while (fb[i] != 0 and (fb[i] != '/' or fb[i - 1] != '*')) : (i += 1) {
                if (fb[i] == '\n') lineno += 1;
            }
            i += 1;
            if (fb[i] != 0) continue :scanning;
        }
        if (p_print) std.debug.print("tstart == {d} '{u}' ", .{ i, fb[i] });
        ps.tokenstart = i; // Mark the beginning of the token
        ps.tokenlineno = lineno; // Linenumber on which token begins
        if (fb[i] == '"') { // String literals
            i += 1;
            while (fb[i] != 0 and fb[i] != '"') : (i += 1) {
                if (fb[i] == '\n') lineno += 1;
            }
            if (fb[i] == 0) {
                ErrorMsg(ps.filename, ps.tokenlineno, "" ++
                    "String starting on this line is not terminated before " ++
                    "the end of the file.", .{});
                ps.errorcnt += 1;
                break :scanning;
            } else {
                skip = true;
            }
        } else if (fb[i] == '{') { // A block of C code
            var level: usize = 1;
            i += 1;
            while (fb[i] != 0 and (level > 1 or fb[i] != '}')) : (i += 1) {
                if (fb[i] == '\n') lineno += 1 //
                else if (fb[i] == '{') level += 1 //
                else if (fb[i] == '}') level -= 1 //
                else if (fb[i] == '/' and i + 1 < fb.len and fb[i + 1] == '*') {
                    // Skip C comments
                    i += 2;
                    var prev: u8 = 0;
                    while (fb[i] != 0 and (fb[i] != '/' or prev != '*')) : (i += 1) {
                        if (fb[i] == '\n') lineno += 1;
                        prev = fb[i];
                    }
                } else if (fb[i] == '/' and fb[i + 1] == '/') {
                    // Skip C++ comments too
                    i += 2;
                    while (fb[i] != 0 and fb[i] != '\n') : (i += 1) {}
                } else if (fb[i] == '"' or fb[i] == '\'') {
                    // String or character literals (since the latter can have " in it)
                    const startchar = fb[i];
                    var prevc: u8 = 0;
                    i += 1;
                    while (fb[i] != 0 and (fb[i] != startchar or prevc == '\\')) : (i += 1) {
                        if (fb[i] == '\n') lineno += 1;
                        if (prevc == '\\')
                            prevc = 0
                        else
                            prevc = fb[i]; // clever
                    }
                }
            }
            if (i == fb.len and fb[i - 1] != '}') {
                ErrorMsg(ps.filename, ps.tokenlineno, "" ++
                    "C code starting on this line is not terminated before " ++
                    "the end of the file.", .{});
                ps.errorcnt += 1;
            } else {
                skip = true; // Clip end of C blocks also
            }
        } else if (isAlnum(fb[i])) {
            while (fb[i] != 0 and (isAlnum(fb[i]) or fb[i] == '_')) : (i += 1) {}
        } else if (i + 2 < fb.len and fb[i] == ':' and fb[i + 1] == ':' and fb[i + 2] == '=') {
            i += 3;
        } else if (fb[i] == '/' or fb[i] == '|' and isAlpha(fb[i + 1])) {
            i += 2;
            while (fb[i] != 0 and (isAlnum(fb[i]) or fb[i] == '_')) : (i += 1) {}
        } else { //  All other (one character) operators
            i += 1;
        }
        const x = fb[ps.tokenstart..i];
        if (p_print) std.debug.print("i == {d} '{u}' ", .{ i, fb[i] });
        try parseonetoken(ps, x);
        if (p_print) std.debug.print("skip: {any} ", .{skip});
        if (skip) i += 1; // End byte of string and code tokens.
    }
}

//| [5230] Set manipulation
//|
//| This is actually pretty straightforward, we use a []bool instead of a
//| *char but same same.  It can probably be refined later but honestly
//| space efficiency is not a big deal (in that I DEFINITELY DO NOT need
//| to beat lemon.c there), and byte booleans are going to be faster than
//| bitsets, if anything.  Then again, I would get union for free, not that
//| it's an especially recondite algorithm...

threadlocal var set_size: usize = 0;

fn SetSize(n: usize) void {
    set_size = n + 1;
}

//| SetNew is just allocating []bool, SetFree needs the allocator so we
//| take care of it when destroying things with sets on them.

// Add a new element to the set.  Return `true` if the element was added
// and `false` if it was already there.
fn SetAdd(set: []bool, n: usize) bool {
    const was = set[n];
    assert(n < set_size);
    set[n] = true;
    return !was;
}

/// Add every element of s2 to s1.  Return `true` if s1 changes.
fn SetUnion(s1: []bool, s2: []bool) bool {
    assert(s1.len == s2.len);
    var changed = false;
    for (0..s1.len) |i| {
        if (!s2[i]) continue;
        if (!s1[i]) {
            changed = true;
            s1[i] = true;
        }
    }
    return changed;
}

pub fn main() !void {
    // We begin, as always, with the Allocator Dance
    var dbga: std.heap.DebugAllocator(.{}) = .init;
    defer {
        assert(.ok == dbga.deinit());
    }
    // TODO: Use dbga for debug builds and page otherwise, use smp (?!)
    // for not-pools.

    // Set up pools.
    const allocator = dbga.allocator();
    action_allocator = ActionAllocator.init(std.heap.page_allocator);
    defer action_allocator.deinit();
    Configlist_init(allocator, .init(std.heap.page_allocator));
    defer cf_ls.pool.deinit();
    cf_ls.allocator = allocator;
    plink_freelist = .init(std.heap.page_allocator);
    is_plink_freelist = true;
    defer {
        plink_freelist.deinit();
        is_plink_freelist = false;
    }
    try plink_freelist.preheat(100);
    Strsafe_init(allocator);
    defer Strsafe_free();
    Symbol_init(allocator);
    defer Symbol_free();

    defer {
        // Some rare symbols 'spill', because they can't be
        // stored in the Symbol intern map, we we free those
        // here.
        while (sym_freelist) |free| {
            free.sp.destroy(allocator);
            sym_freelist = free.next;
            allocator.destroy(free);
        }
    }

    // These need to exist so that some later argument parser can
    // assign them.  That that point of course, variable, but one
    // damn thing at a damn time.
    const version = false;
    const rpflag = false;
    const basisflag = false;
    const compress = false;
    const quiet = false;
    const statistics = false;
    const mhflag = false;
    const nolinenosflag = false;
    const noResort = false;
    const sqlFlag = false;
    const printPP = false;
    // Reconcile Zig to this unfortunate situation:
    _ = .{ version, rpflag, basisflag, compress, quiet, statistics, mhflag, nolinenosflag, noResort, sqlFlag, printPP };

    const args = try std.process.argsAlloc(allocator);
    // TODO: Quirk-compatible flags parser.  Do this last-ish.
    // [1636-1689] - todo
    defer std.process.argsFree(allocator, args);
    const filename: []const u8 = file: {
        if (args.len >= 1) {
            break :file args[1];
        } else {
            std.debug.print("lemon.zig needs a filename\n", .{});
            std.process.exit(1);
        }
    };
    var lem = try Lemon.create(allocator);
    defer lem.destroy(allocator);
    lem.argv = args;
    lem.filename = filename;
    lem.basisflag = basisflag;
    lem.nolineosflag = nolinenosflag;
    lem.printPreprocessed = printPP;
    _ = try Symbol_new("$"); // Why?
    // TODO: Write a full parse file and move the file opening stuff there,
    // with the Pstate, etc.
    var pstate = try PState.create(allocator, lem);
    defer pstate.destroy();
    pstate.gp = lem;
    pstate.filename = filename;

    try Parse(pstate);
    if (lem.printPreprocessed or lem.errorcnt > 0) {
        logger.err("exiting due to preprocess only or too many errors", .{});
        exit(@truncate(lem.errorcnt));
    }
    if (lem.nrule == 0) {
        logger.err("Empty grammar.", .{});
        exit(1);
    }
    lem.errsym = Symbol_find("error");

    // Count and index the symbols of the grammar
    _ = try Symbol_new("{default}");
    lem.symbols = Symbol_arrayof();
    sort(*Symbol, lem.symbols, {}, Symbol_lessThanFn);
    if (p_symbols) for (lem.symbols) |symbol| {
        std.debug.print("{s} ", .{symbol.name});
    };
    for (lem.symbols, 0..) |sym, i| {
        sym.index = @intCast(i);
    }
    {
        var i: usize = lem.symbols.len;
        while (lem.symbols[i - 1].type == .multiterminal) : (i -= 1) {}
        dbgassert(strcmp(lem.symbols[i - 1].name, "{default}"));
        lem.nsymbol = i - 1;
        i = 1;
        while (isUpper(lem.symbols[i].name[0])) : (i += 1) {}
        lem.nterminal = i;
    }
    sequenceRules(lem);
    // [1726]
    // /* Generate a reprint of the grammar, if requested on the command line */
    // else
    //
    SetSize(lem.nterminal + 1);
    // Find the precedence for every production rule (that has one)
    FindRulePrecedences(lem);
    if (p_check or p_symbols) {
        dprint("Sorted rules: {s}\n", .{lem.filename});
        var rp: ?*Rule = lem.rule;
        while (rp) |rule| : (rp = rule.next) {
            dprint("{s} ({d})  ", .{ rule.lhs.name, rule.iRule });
        }
        dprint("\n", .{});
    }
    // Compute the lambda-nonterminals and the first-sets for every
    // nonterminal
    try FindFirstSets(lem);
    if (p_check) {
        var rp: ?*Rule = lem.rule;
        while (rp) |rule| : (rp = rule.next) {
            const s1 = rule.lhs;
            dprint("lhs: {s} ({d})", .{ s1.name, s1.index });
            if (s1.lambda) {
                dprint(" LAMBDA ", .{});
            }
            for (s1.firstset) |b| {
                if (b) {
                    dprint("+", .{});
                } else {
                    dprint(".", .{});
                }
            }
            dprint("\n", .{});
            for (rule.rhs, 0..) |s2, i| {
                dprint("  {d}:{s} ({d})\n", .{ i, s2.name, s2.index });
            }
        }
    }
    dbgassert(lem.nstate == 0);
    // Compute all LR(0) states.  Also record follow-set propagation
    // links so that the follow-set can be computed later
    try FindStates(lem);
    { // This is the bulk of the remaining work:
        // /* Compute all LR(0) states.  Also record follow-set propagation
        // ** links so that the follow-set can be computed later */
        //  lem.nstate = 0;
        // FindStates(&lem);
        // lem.sorted = State_arrayof();
        //
        // /* Tie up loose ends on the propagation links */
        // FindLinks(&lem);
        //
        // /* Compute the follow set of every reducible configuration */
        // FindFollowSets(&lem);
        //
        // /* Compute the action tables */
        // FindActions(&lem);
        //
        // /* Compress the action tables */
        // if( compress==0 ) CompressTables(&lem);
        //
        // /* Reorder and renumber the states so that states with fewer choices
        // ** occur at the end.  This is an optimization that helps make the
        // ** generated parser tables smaller. */
        // if( noResort==0 ) ResortStates(&lem);
        //
        // /* Generate a report of the parser generated.  (the "y.output" file) */
        // if( !quiet ) ReportOutput(&lem);
        //
        // /* Generate the source code for the parser */
        // ReportTable(&lem, mhflag, sqlFlag);
        //
        // /* Produce a header file for use by the scanner.  (This step is
        // ** omitted if the "-m" option is used because makeheaders will
        // ** generate the file for us.) */
        // if( !mhflag ) ReportHeader(&lem);
    }
    // The finale looks like this:
    //
    // if( statistics ){
    //   printf("Parser statistics:\n");
    //   stats_line("terminal symbols", lem.nterminal);
    //   stats_line("non-terminal symbols", lem.nsymbol - lem.nterminal);
    //   stats_line("total symbols", lem.nsymbol);
    //   stats_line("rules", lem.nrule);
    //   stats_line("states", lem.nxstate);
    //   stats_line("conflicts", lem.nconflict);
    //   stats_line("action table entries", lem.nactiontab);
    //   stats_line("lookahead table entries", lem.nlookaheadtab);
    //   stats_line("total table size (bytes)", lem.tablesize);
    // }
    // if( lem.nconflict > 0 ){
    //   fprintf(stderr,"%d parsing conflicts.\n",lem.nconflict);
    // }
    //
    // /* return 0 on success, 1 on failure. */
    // exitcode = ((lem.errorcnt > 0) || (lem.nconflict > 0)) ? 1 : 0;
    // exit(exitcode);
    // return (exitcode);
    //
    // Which is adequately straightforward imho.
    //
    std.process.cleanExit();
}

//| [1809] MergeSort
//|
//| This will be the sharpest deviation from Lemon.  Although the technique
//| used to achieve a type-generic merge sort is feasible in Zig (and is
//| very clever), we're better off returning a brace of functions, given the
//| type information we need.
//|
//| We take the type, the name of the field pointing to the next item in the
//| list, and a compare function which returns true if a is `<=` b.  The
//| equality tie-breaker is important, because it gives us sort stability.
//|
//| We then specialize the functions accordingly, returning the one we need.
//|
//| NOTE: to self: when you port this to Zelda, use std.math.Order, so we
//| can add sorts in both directions and they'll both be stable.

const LISTSIZE = 32;

fn mergeSortFn(
    T: type,
    comptime next: []const u8,
    lteFn: fn (a: *T, b: *T) bool,
) fn (*T) *T {
    return struct {
        /// Takes a pointer to *T, the head of a linked list found with
        /// t.next.  Merge sorts the list, returning a pointer to the
        /// head of a sorted list containing the elements of the passed-
        /// in list.
        pub fn msort(a: *T) *T {
            var ep: ?*T = null;
            var set: [LISTSIZE]?*T = .{null} ** LISTSIZE;
            var maybe_list: ?*T = a;
            while (maybe_list) |list| {
                ep = list;
                maybe_list = @field(list, next);
                @field(ep.?, next) = null;
                var i: usize = 0;
                stripe: while (set[i] != null) : ({
                    if (i == LISTSIZE - 1) break :stripe;
                    i += 1;
                }) {
                    ep = merge(ep, set[i]);
                    set[i] = null;
                }
                set[i] = ep;
            }
            ep = null;
            for (0..LISTSIZE) |i| {
                if (set[i]) |tail| {
                    ep = merge(tail, ep);
                }
            }
            return ep.?;
        }

        // Merge two linked lists, given the head. Either the first or the
        // second may be null: by construction, they will never both be
        // null, but it's harmless to our purposes to return a `?*T`, so
        // we wouldn't benefit from that fact and don't take advantage of it.
        fn merge(maybe_a: ?*T, maybe_b: ?*T) ?*T {
            if (maybe_a == null) return maybe_b;
            if (maybe_b == null) return maybe_a;
            var a: ?*T = maybe_a;
            var b: ?*T = maybe_b;
            const head: *T = if (lteFn(a.?, b.?)) head: {
                const h = a.?;
                a = @field(h, next);
                break :head h;
            } else head: {
                const h = b.?;
                b = @field(h, next);
                break :head h;
            };
            var ptr: *T = head;
            while (a) |a_ptr| while (b) |b_ptr| {
                if (lteFn(a_ptr, b_ptr)) {
                    @field(ptr, next) = a_ptr;
                    ptr = a_ptr;
                    a = @field(a_ptr, next);
                } else {
                    @field(ptr, next) = b_ptr;
                    ptr = b_ptr;
                    b = @field(b_ptr, next);
                }
            };
            if (a) |a_ptr| {
                @field(ptr, next) = a_ptr;
            } else {
                @field(ptr, next) = b;
            }
            return head;
        }
    }.msort;
}

fn sequenceRules(lem: *Lemon) void {
    // Assign sequential rule numbers.  Start with 0.  Put rules that have no
    // reduce action C-code associated with them last, so that the switch()
    // statement that selects reduction actions will have a smaller jump table.
    // NOTE: the original code does all this assigning, then sorts. I don't
    // see why, since we create the order right here.  We can just:
    var rnum: usize = 0;
    var rp: ?*Rule = lem.rule;
    var action_head: ?*Rule = null;
    var action_tail: ?*Rule = null;
    var no_act_head: ?*Rule = null;
    var no_act_tail: ?*Rule = null;
    while (rp) |rule| : (rp = rule.next) {
        if (rule.code.len > 0) {
            rule.iRule = @intCast(rnum);
            rnum += 1;
            if (action_head == null) {
                action_head = rule;
                action_tail = rule;
            } else {
                // By the above, we have the action
                // tail, so
                action_tail.?.next = rule;
                action_tail = rule;
            }
        } else {
            if (no_act_head == null) {
                no_act_head = rule;
                no_act_tail = rule;
            } else {
                no_act_tail.?.next = rule;
                no_act_tail = rule;
            }
        }
    } // Cut the tails:
    if (action_tail) |act_tail| act_tail.next = null;
    if (no_act_tail) |no_act| no_act.next = null;
    lem.nruleWithAction = rnum;
    rp = no_act_head; // This works correctly even if there are no no-action rules
    while (rp) |rule| : (rp = rule.next) {
        dbgassert(rule.code.len == 0);
        rule.iRule = @intCast(rnum);
        rnum += 1;
    }
    lem.startRule = lem.rule;
    // We must have at least one rule, or we bailed already, so this works too:
    lem.rule = if (action_head) |act_head| act_head else no_act_head.?;
    if (action_head) |_| {
        // Means we have an action_tail too:
        action_tail.?.next = no_act_head;
        dbgassert(no_act_tail != null and no_act_tail.?.next == null);
    } // Sorted!
    rp = lem.startRule;
    if (builtin.mode == .Debug) while (rp) |rule| : (rp = rule.next) {
        if (rule.next) |next| {
            dbgassert(rule.iRule + 1 == next.iRule);
        }
    };
}

//| Global State
//
// lemon.c uses some judicious static globals, and if only to
// ease porting, lemon.zig does likewise.
//
// I will want to 'modularize' zitron, so that it can be, in
// particular, compiled to WASM and run in the browser.  But
// that can wait.  I might even give lemon.zig the same
// treatment for the same reason, I really don't know enough
// about WASM to say if that would even help.  I'm sure I've
// seen "programs" which would have a main function running
// in the browser, so surely there's an affordance for it.

threadlocal var str_safe: StrSafe = undefined;
threadlocal var is_a_strsafe: bool = false;

const StrSafe = struct {
    safe: StringArrayHashMap(void),
    allocator: Allocator,

    pub fn init(allocator: Allocator) StrSafe {
        return .{ .allocator = allocator, .safe = .empty };
    }

    pub fn find(strsafe: *StrSafe, key: []const u8) ?[]const u8 {
        return strsafe.safe.getKey(key);
    }

    pub fn intern(strsafe: *StrSafe, k: []const u8) ![]const u8 {
        if (strsafe.safe.getKey(k)) |key| {
            return key;
        }
        const dupe = try strsafe.allocator.dupe(u8, k);
        try strsafe.safe.put(strsafe.allocator, dupe, {});
        return dupe;
    }
};

fn Strsafe_init(allocator: Allocator) void {
    if (is_a_strsafe) return; // I don't think this happens..
    defer is_a_strsafe = true;
    str_safe = .init(allocator);
}

fn Strsafe(data: []const u8) ![]const u8 {
    dbgassert(is_a_strsafe);
    return str_safe.intern(data);
}

fn Strsafe_find(key: []const u8) ?[]const u8 {
    dbgassert(is_a_strsafe);
    return str_safe.find(key);
}

fn Strsafe_free() void {
    dbgassert(is_a_strsafe);
    defer is_a_strsafe = false;
    // strsafe owns all interned strings:
    for (str_safe.safe.keys()) |str| {
        str_safe.allocator.free(str);
    }
    str_safe.safe.deinit(str_safe.allocator);
}

//| Symbols
//|

const SymbolSafe = struct {
    safe: StringArrayHashMap(*Symbol),
    allocator: Allocator,

    pub fn intern(symsafe: *SymbolSafe, x: []const u8) !*Symbol {
        if (symsafe.safe.get(x)) |sym| {
            return sym;
        }
        try symsafe.safe.ensureUnusedCapacity(symsafe.allocator, 1);
        const sp = try Symbol.create(symsafe.allocator, x);
        symsafe.safe.putAssumeCapacity(x, sp);
        return sp;
    }
};

//| Some symbols (due to multiterminals) have the same name as others,
//| specifically their [0] subsym. So we can't keep them in the SymbolSafe:
//| we create a separate freelist to store them.

const SymFreelist = struct {
    sp: *Symbol,
    next: ?*SymFreelist,
};

threadlocal var sym_freelist: ?*SymFreelist = null;

threadlocal var symbol_map: SymbolSafe = undefined;
threadlocal var is_symbol_map = false;

fn Symbol_init(allocator: Allocator) void {
    if (is_symbol_map) return;
    defer is_symbol_map = true;
    symbol_map.allocator = allocator;
    symbol_map.safe = .empty;
}

fn Symbol_free() void {
    dbgassert(is_symbol_map);
    defer is_symbol_map = false;
    for (symbol_map.safe.values()) |v| {
        v.destroy(symbol_map.allocator);
    }
    symbol_map.safe.deinit(symbol_map.allocator);
}

fn Symbol_new(str: []const u8) !*Symbol {
    dbgassert(is_symbol_map);
    return symbol_map.intern(str);
}

fn Symbol_count() usize {
    return symbol_map.safe.count();
}

fn Symbol_find(str: []const u8) ?*Symbol {
    dbgassert(is_symbol_map);
    return symbol_map.safe.get(str);
}

fn Symbol_arrayof() []*Symbol {
    dbgassert(is_symbol_map);
    return symbol_map.safe.values();
}

// /* Compare two symbols for sorting purposes.  Return negative,
// ** zero, or positive if a is less then, equal to, or greater
// ** than b.
// **
// ** Symbols that begin with upper case letters (terminals or tokens)
// ** must sort before symbols that begin with lower case letters
// ** (non-terminals).  And MULTITERMINAL symbols (created using the
// ** %token_class directive) must sort at the very end. Other than
// ** that, the order does not matter.
// **
// ** We find experimentally that leaving the symbols in their original
// ** order (the order they appeared in the grammar file) gives the
// ** smallest parser tables in SQLite.
// */

//| [5840]
//
fn Symbol_lessThanFn(_: void, a: *Symbol, b: *Symbol) bool {
    const a_val: u8 = if (a.type == .multiterminal) 3 else if (a.name[0] > 'Z') 2 else 1;
    const b_val: u8 = if (b.type == .multiterminal) 3 else if (b.name[0] > 'Z') 2 else 1;
    if (a_val < b_val) return true else if (a_val > b_val) return false;
    return (a.index < b.index);
}

//| [1300] configlist.c
//|
//| This is one of the places where the Lemon generator uses global state.
//| No sin in that, not in an application, but we're going to package it up
//| into:

pub const ConfigLists = struct {
    allocator: Allocator,
    pool: MemoryPool(Config),
    current: ?*Config,
    currentend: *?*Config,
    basis: ?*Config,
    basisend: *?*Config,
    config_table: ArrayHashMap(*Config, void, ConfigContext, false),
};

const ConfigContext = struct {
    pub fn eql(_: ConfigContext, c1: *Config, c2: *Config, _: usize) bool {
        return c1.rp.index == c2.rp.index and c1.dot == c2.dot;
    }

    // [5822]
    pub fn hash(_: ConfigContext, c: *Config) u32 {
        // This is where I brag just a little, having spotted an error
        // of no practical significance in lemon.c as it was when I
        // began this:  https://sqlite.org/forum/forumpost/686cb52ae2
        //
        return @intCast(c.rp.index * 37 + c.dot);
    }
};

//| so we only need one global:
threadlocal var cf_ls: ConfigLists = undefined;
threadlocal var is_a_configlists = false;

fn newconfig() !*Config {
    dbgassert(is_a_configlists);
    const cp = try cf_ls.pool.create();
    cp.* = .empty;
    return cp;
}

fn deleteconfig(cfp: *Config) void {
    dbgassert(is_a_configlists);
    cf_ls.pool.destroy(cfp);
}

fn Configlist_init(allocator: Allocator, pool: MemoryPool(Config)) void {
    if (is_a_configlists) return;
    defer is_a_configlists = true;
    cf_ls.allocator = allocator;
    cf_ls.pool = pool;
    cf_ls.current = null;
    cf_ls.currentend = &cf_ls.current;
    cf_ls.basis = null;
    cf_ls.basisend = &cf_ls.basis;
    cf_ls.config_table = .empty;
}

fn Configlist_reset() void {
    dbgassert(is_a_configlists);
    cf_ls.current = null;
    cf_ls.currentend = &cf_ls.current;
    cf_ls.basis = null;
    cf_ls.basisend = &cf_ls.basis;
    cf_ls.config_table.clearRetainingCapacity();
}

/// Add another configuration to the configuration list
fn Configlist_add(rp: *Rule, dot: u32) !*Config {
    dbgassert(is_a_configlists);
    var model: Config = undefined;
    model.rp = rp;
    model.dot = dot;
    const maybe_cfp = cf_ls.config_table.getKey(&model);
    if (maybe_cfp) |cfp| return cfp;
    var cfp = try newconfig();
    cfp.rp = rp;
    cfp.dot = dot;
    cfp.fws = try cf_ls.allocator.alloc(bool, set_size);
    @memset(cfp.fws, false);
    cf_ls.currentend.* = cfp;
    cf_ls.currentend = &cfp.next;
    try cf_ls.config_table.put(cf_ls.allocator, cfp, {});
    return cfp;
}

fn Configlist_addbasis(rp: *Rule, dot: u32) !*Config {
    dbgassert(is_a_configlists);
    var model: Config = undefined;
    model.rp = rp;
    model.dot = dot;
    const maybe_cfp = cf_ls.config_table.getKey(&model);
    if (maybe_cfp) |cfp| return cfp;
    var cfp = try newconfig();
    cfp.rp = rp;
    cfp.dot = dot;
    cfp.fws = try cf_ls.allocator.alloc(bool, set_size);
    @memset(cfp.fws, false);
    cf_ls.currentend.* = cfp;
    cf_ls.currentend = &cfp.next;
    cf_ls.basisend.* = cfp;
    cf_ls.basisend = &cfp.bp;
    try cf_ls.config_table.put(cf_ls.allocator, cfp, {});
    return cfp;
}

// [5642]
//
/// Compare two configurations
fn Configcmp(a: *Config, b: *Config) bool {
    if (a.rp.index < b.rp.index) {
        return true;
    } else if (a.rp.index > b.rp.index) {
        return false;
    } else if (a.dot <= b.dot) {
        return true;
    } else {
        return false;
    }
}

/// Compute the closure of the configuration list
fn Configlist_closure(lemp: *Lemon) !void {
    var this_cfp: ?*Config = cf_ls.current;
    scan: while (this_cfp) |cfp| : (this_cfp = cfp.next) {
        const rp = cfp.rp;
        const dot = cfp.dot;
        if (dot >= rp.nrhs) continue :scan;
        const sp = rp.rhs[dot];
        if (sp.rule == null and sp != lemp.errsym) {
            ErrorMsg(lemp.filename, 0, "" ++
                "Nonterminal \"{s}\" has no rules.", .{sp.name});
            lemp.errorcnt += 1;
        }
        var this_newrp = sp.rule;
        while (this_newrp) |newrp| : (this_newrp = newrp.nextlhs) {
            const newcfp = try Configlist_add(newrp, 0);
            dots: for (dot + 1..rp.nrhs) |i| {
                const xsp = rp.rhs[i];
                // TODO: refactor this: slice in for loop above,
                // switch statement here:
                if (xsp.type == .terminal) {
                    _ = SetAdd(newcfp.fws, xsp.index);
                    break :dots;
                } else if (xsp.type == .multiterminal) {
                    for (xsp.subsym) |subsym| {
                        _ = SetAdd(newcfp.fws, subsym.index);
                    }
                    break :dots;
                } else {
                    _ = SetUnion(newcfp.fws, xsp.firstset);
                    if (!xsp.lambda) break :dots;
                }
                if (i == rp.nrhs) try Plink_add(&cfp.fplp, newcfp);
            }
        }
    }
}

const Configlist_msort = mergeSortFn(Config, "next", Configcmp);

fn Configlist_sort() void {
    cf_ls.current = if (cf_ls.current) |cfp| Configlist_msort(cfp) else null;
    cf_ls.currentend.* = null;
}

const Configlist_msortBasis = mergeSortFn(Config, "bp", Configcmp);

fn Configlist_sortbasis() void {
    cf_ls.basis = if (cf_ls.basis) |bp| Configlist_msortBasis(bp) else null;
    cf_ls.basisend.* = null;
}
/// Return a pointer to the head of the configuration list
/// and reset the list.
fn Configlist_return() ?*Config {
    const old = cf_ls.current;
    cf_ls.current = null;
    cf_ls.currentend.* = null;
    return old;
}

/// Return a pointer to the head of the configuration basis list
/// and reset the list.
fn Configlist_basis() ?*Config {
    const old = cf_ls.basis;
    cf_ls.basis = null;
    cf_ls.basisend.* = null;
    return old;
}

/// Free all elements of the given configuration list.
fn Configlist_eat(cfp: ?*Config, allocator: Allocator) void {
    var nextcfp: ?*Config = cfp;
    while (nextcfp) |this_cfp| {
        nextcfp = this_cfp.next;
        assert(this_cfp.fplp == null);
        assert(this_cfp.bplp == null);
        if (this_cfp.fws.len > 0) allocator.free(this_cfp.fws);
        deleteconfig(this_cfp);
    }
}

test "exe mentioned" {
    std.debug.print("hello from lemon main\n", .{});
}
