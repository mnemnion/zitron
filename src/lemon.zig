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

const assert = std.debug.assert;

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
    index: int,
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
    destLineno: int,
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
    nsubsym: int, // Probably redundant with this slice:
    /// Array (slice) of constituent symbols
    subsym: []*Symbol,

    pub const empty: Symbol = std.mem.zeroInit(Symbol, .{});
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
    ruleline: int, // Unsigned, duh
    /// The RHS symbols
    rhs: []*Symbol,
    /// Number of RHS symbols
    nrhs: usize, // NOTE: This should use rule.rhs.len, eventually.

    /// An alias for each RHS symbol (empty if none)
    rhsalias: [][]u8, // Const?
    /// Line number at which code begins
    line: int,
    /// The code executed when this rule is reduced
    code: []const u8,
    /// Setup code before code[] above
    codePrefix: []const u8,
    /// Breakdown code after code[] above
    codeSuffix: []const u8,
    /// Precedence symbol for this rule
    precsym: ?*Symbol,
    /// An index number for this rule
    index: int,
    /// Rule number as used in the generated tables
    iRule: int,
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
    dot: int,
    /// Follow-set for this configuration only
    fws: []bool,
    /// Follow-set forward propagation links
    fplp: ?*PLink = null,
    /// Follow-set backwards propagation links
    bplp: ?*PLink = null,
    /// Pointer to state which contains this
    stp: ?*State = null,
    /// used during followset and shift computations
    status: ConfigStatus = .incomplete,
    /// Next configuration in the state
    next: ?*Config = null,
    /// The next basis configuration
    bp: ?*Config = null,
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
    pb: *Config,
    /// All configurations in this set
    cfp: *Config,
    /// Sequential number for this state
    statenum: int,
    /// List of actions for this state
    ap: *Action,
    /// Number of actions on terminals
    nTknAct: u32,
    /// Number of actions on nonterminals
    nNtAct: u32,
    /// yy_action[] offset for terminals
    iTnkOfst: ?u32,
    /// yy_action[] offset for nonterminals
    iNtOfst: ?u32,
    /// Default action is to REDUCE by this rule
    iDfltReduce: int,
    /// The default REDUCE rule.
    pDefltReduce: ?*Rule,
    /// True if this is an auto-reduce state
    autoreduce: bool,

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

/// A followset propagation link indicates that the contents of one
/// configuration followset should be propagated to another whenever
/// the first changes.
const PLink = struct {
    /// The configuration to which linked
    cfp: *Config,
    /// The next propagate link
    next: *?PLink,
};

/// The state vector for the entire parser generator is recorded as
/// follows.  (LEMON uses no global variables and makes little use of
/// static variables.  Fields in the following structure can be thought
/// of as being global variables in the program.)
const Lemon = struct {
    /// Table of states sorted by state number
    sorted: []*State,
    /// List of all rules
    rule: *Rule,
    /// First rule
    startRule: *Rule,
    ///.Number of states
    nstate: int,
    /// nstate with tail degenerate states removed
    nxstate: int,
    /// Number of rules
    nrule: int,
    /// Number of rules with actions
    nruleWithAction: int,
    /// Number of terminal and nonterminal symbols
    nsymbol: int,
    /// Number of terminal symbols
    nterminal: int,
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
    errorsym: ?*Symbol,
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
    filename: []u8,
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
    argv: [][]u8,
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

//| ... but we'll make it 'global' for now:
threadlocal var cfgl: ConfigLists = undefined;

fn newconfig() !*Config {
    return cfgl.pool.create();
}

fn ConfigList_init(allocator: Allocator, pool: MemoryPool(Config)) void {
    cfgl.allocator = allocator;
    cfgl.pool = pool;
    cfgl.current = null;
    cfgl.currentend = &cfgl.current;
    cfgl.basis = null;
    cfgl.basisend = &cfgl.basis;
    cfgl.config_table = .empty;
}

fn ConfigList_reset() void {
    cfgl.current = null;
    cfgl.currentend = &cfgl.current;
    cfgl.basis = null;
    cfgl.basisend = &cfgl.basis;
    cfgl.config_table.clearRetainingCapacity();
}

/// Add another configuration to the configuration list
fn Configlist_add(rp: *Rule, dot: int) !*Config {
    var model: Config = undefined;
    model.rp = rp;
    model.dot = dot;
    const maybe_cfp = cfgl.config_table.getKey(&model);
    if (maybe_cfp) |cfp| return cfp;
    var cfp = try newconfig();
    cfp.* = .{};
    cfp.rp = rp;
    cfp.dot = dot;
    cfp.fws = try cfgl.allocator.alloc(bool, set_size);
    @memset(cfp.fws, false);
    cfgl.currentend.* = cfp;
    cfgl.currentend = &cfp.next;
    cfgl.config_table.put(cfgl.allocator, cfp, {});
    return cfp;
}

fn Configlist_addbasis(rp: *Rule, dot: int) !void {
    var model: Config = undefined;
    model.rp = rp;
    model.dot = dot;
    const maybe_cfp = cfgl.config_table.getKey(&model);
    if (maybe_cfp) |cfp| return cfp;
    var cfp = try newconfig();
    cfp.* = .{};
    cfp.rp = rp;
    cfp.dot = dot;
    cfp.fws = try cfgl.allocator.alloc(bool, set_size);
    @memset(cfp.fws, false);
    cfgl.currentend.* = cfp;
    cfgl.currentend = cfp.next;
    cfgl.basisend.* = cfp;
    cfgl.basisend = &cfp.bp;
    cfgl.config_table.put(cfgl.allocator, cfp, {});
    return cfp;
}

// TODO: Configlist_closure(lemp: *Lemon) void {}
// Configlist_sort
// Configlist_sortbasis
// Configlist_return
// Configlist_basis
// Configlist_eat

//| [1500] ErrorMsg

fn ErrorMsg(filename: []const u8, lineno: usize, comptime fmt: []const u8, args: anytype) !void {
    std.debug.print("{s}:{d}", .{ filename, lineno });
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
    tokenlineno: int,
    /// Number of errors so far
    errorcnt: int,
    /// Text of current token
    tokenstart: []const u8,
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
    nrhs: int,
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
    decllinenoslot: ?*int,
    /// Assign this association to decl arguments
    declassoc: E_Assoc,
    /// Assign this precedence to decl arguments
    preccounter: u16,
    /// Pointer to first rule in the grammar
    firstrule: ?*Rule,
    /// Pointer to the most recently parsed rule
    lastrule: ?*Rule,
    /// String intern pool
    strsafe: StrSafe,

    pub const empty: PState = .{
        .allocator = undefined,
        .filename = "",
        .tokenlineno = 0,
        .errorcnt = 0,
        .gp = undefined,
        .state = .initialize,
        .fallback = null,
        .tkclass = &Symbol.empty,
        .lhs = &Symbol.empty,
        .lhsalias = &Symbol.empty,
        .nrhs = 0,
        .rhs = &.{},
        .alias = &.{""},
        .prevrule = null,
        .declkeyword = "",
        .declargslot = null,
        .insertLineMacro = false,
        .decllinenoslot = null,
        .declassoc = .unk,
        .preccounter = 0,
        .firstrule = null,
        .lastrule = null,
        .strsafe = undefined,
    };

    pub fn create(allocator: Allocator, gp: *Lemon, strsafe: StrSafe) !*PState {
        var psp = try allocator.create(PState);
        psp.* = .empty;
        psp.allocator = allocator;
        psp.gp = gp;
        psp.strsafe = strsafe;
        return psp;
    }

    // No clue how to dispose of things yet. But I think the answer is that Symbols all
    // live in the intern pool, with the strings, and we just nuke 'em at the end.
    // So...

    pub fn destroy(ps: *PState) void {
        ps.allocator.destroy(ps);
    }
};

const StrSafe = struct {
    safe: StringArrayHashMap(void),
    allocator: Allocator,

    pub fn init(allocator: Allocator) StrSafe {
        return .{ .allocator = allocator, .safe = .empty };
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

fn parseonetoken(psp: *PState) !void {
    const x = try psp.strsafe.intern(psp.tokenstart);
    // This seems to be presumed (?)
    assert(x.len != 0);
    state: switch (psp.state) {
        .initialize => { // TODO: Probably just do this first yeah
            psp.prevrule = null;
            psp.prevcounter = 0;
            psp.firstrule, psp.lastrule = .{ null, null };
            psp.gp.nrule = 0;
            continue :state .waiting_for_decl_keyword;
        },
        .waiting_for_decl_or_rule => {
            if (x[0] == '%') {
                psp.state = .waiting_for_decl_keyword;
            } else if (isLower(x[0])) {
                // psp.lhs = Symbol_new(x);
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
                        // TODO: only appearance of NEVER-REDUCE in lemon or lempar. Impossibru?
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
                const rp = try psp.allocator.create(Rule);
                rp.* = .empty;
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
                    psp.lastrule.next = rp;
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
                    psp.rhs[psp.nrhs] = Symbol_new(x);
                    psp.alias[psp.nrhs] = "";
                    psp.nrhs += 1;
                }
            } else if ((x[0] == '|' or x[0] == '/') and psp.nrhs > 0 and x.len > 0 and isUpper(x[1])) {
                const msp = psp.rhs[psp.nrhs - 1];
                if (msp.type != .multiterminal) {
                    const origmsp = msp;
                    msp = try psp.allocator.create(Symbol);
                    msp.* = .empty;
                    msp.type = .multiterminal;
                    msp.nsubsym = 1;
                    msp.subsym = try psp.allocator.alloc(*Symbol, 1);
                    msp.subsym[0] = origmsp;
                    msp.name = origmsp.name;
                    psp.rhs[psp.nrhs - 1] = msp;
                }
                msp.nsubsym += 1;
                msp.subsym = try psp.allocator.realloc(msp.subsym, msp.subsym.len + 1);
                // We know x[1] exists and is terminal-shaped, so this is valid:
                msp.subsym[msp.nsubsym - 1] = Symbol_new(x[1..]);
                if (isLower(x[1]) || isLower(msp.subsym[0].name[0])) {
                    ErrorMsg(psp.filename, psp.tokenlineno, "" ++
                        "Cannot form a compound containing a non-terminal", .{});
                    psp.errorcnt += 1;
                    psp.state = .resync_after_rule_error;
                }
            } else if (x[0] == '(' and psp.nrhs == 0) {
                psp.state = .rhs_alias_1;
            } else {
                ErrorMsg(psp.filename, psp.tokenlineno, "" ++
                    "Illegal character on RHS of rule: \"{s}\".", .{});
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
                    "Missing \")\" following LHS alias name \"{s}\".", .{});
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
                    psp.insertLineMacro = 0;
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
                    "Symbol %type \"{s}\" already defined", .{});
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
                var zBuffer: [50]u8 = undefined;
                // The code assumes declargslot is pointing at something, so null should be
                // unreachable here:
                const declargslot = psp.declargslot.?;
                const zOld: []const u8 = declargslot.*;
                const zNew = if (x[0] == '"' or x[0] == '{') x[1..] else x;
                var zLine: []u8 = zBuffer[0..0];
                // To close the slice, we have to track bytes written:
                var zIdx: usize = 0;
                // The original code leaves some buffer here, for some reason, so n
                // is not, and will not become, the valid length of declargslot.*
                var n = zOld.len + zNew.len + 20; // For...?
                // Do we need a line macro?
                const addLineMacro = !psp.gp.nolineosflag and
                    psp.insertLineMacro and
                    psp.tokenlineno > 1 and
                    (psp.decllinenoslot == null or psp.decllinenoslot.?.* != 0);
                if (addLineMacro) {
                    var nBack = std.mem.count(u8, psp.filename, "\\");
                    nBack += std.mem.count(u8, psp.filename, '"');
                    zLine = std.fmt.bufPrint(zBuffer, "#line {d} ", .{psp.tokenlineno}) catch |err| {
                        // Should be literally impossible but ¯\_(ツ)_/¯
                        ErrorMsg(psp.filename, psp.tokenlineno, "" ++
                            "Buffer overflow on #line directive print: {s}", .{@errorName(err)});
                        psp.errorcnt += 1;
                        // NOTE: This will leave zLine empty, which is good, but
                        // there has been talk of error catching 'poisoning'
                        // the old result, because I'm doing this deliberately
                        // but it's often a mistake.  That would be a compile
                        // error and can be corrected by resetting zLine to
                        // zBuf[0..0];
                    };
                    n += psp.filename.len + nBack;
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
                if (psp.decllinenoslot != null and psp.decllinenoslot.* == 0) {
                    psp.decllinenoslot.?.* = psp.tokenlineno;
                }
                @memcpy(zBuf[zIdx..][0..zNew.len], zNew);
                zIdx += zNew.len;
                // Finally, we can put a cap on declargslot:
                declargslot.* = zBuf[0..zIdx];
                // Let's check if that spurious 20 actually comes into play:
                if (zIdx != cast(isize, n) - 20) {
                    // TODO: Remove the extra bytes once this pans out.
                    std.debug.print("zIdx is {d} less than n, not 20\n", .{cast(isize, n) - zIdx});
                }
                // I think we need this, otherwise why zOld?
                psp.declargslot = declargslot;
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
                } else if (sp.fallback) {
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
                msp.subsym = try psp.allocator.realloc(msp.subsym, msp.nsubsym);
                msp.subsym[msp.nsubsym.nsubsym - 1] = try Symbol_new(if (!isUpper(x[0])) x else x[1..]);
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

/// Lemon puts the scanner loop in `main`, I prefer it separate.
fn scan(ps: *PState, fb: [:0]const u8) !void {
    var i: usize = 0;
    var lineno: usize = 1;
    var skip: bool = false; // True when we advance one more before loop
    scanning: while (i < fb.len) {
        if (fb[i] == '\n') lineno += 1;
        if (isSpace(fb[i])) continue :scanning; // Skip all whitespace
        // Skip C++ style comments
        if (fb[i] == '/' and fb[i + 1] == '/') {
            i += 2;
            while (fb[i] != '\n' and fb[i] != 0) : (i += 1) {}
            if (fb[i] != 0) {
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
                    var prevc = 0;
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
            while (fb[i] != 0 and isAlnum(fb[i])) : (i += 1) {}
        } else if (i + 2 < fb.len and fb[i] == ':' and fb[i + 1] == ':' and fb[i + 2] == '=') {
            i += 3;
        } else if (fb[i] == '/' or fb[i] == '|' and isAlpha(fb[i + 1])) {
            i += 2;
            while (fb[i] != 0 and (isAlnum(fb[i + 1]) or fb[i + 1] == '_')) : (i += 1) {}
        } else { //  All other (one character) operators
            i += 1;
        }
        const x = fb[ps.tokenstart..i];
        parseonetoken(x);
        if (skip) i += 1; // End byte of string and code tokens.
    }
}

fn Symbol_new(str: []const u8) !*Symbol {
    _ = str;
    return .{}; // XXX: write this
}

fn Symbol_find(str: []const u8) ?*Symbol {
    return Symbol_new(str) catch unreachable; // XXX: write this as well
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

//
//
//
//
//
//
//
//
//
//
//
//
//
//
//
//
//
//
//
//
//
//
//
//
//
//
//
//
//
//
//
//

pub fn main() void {
    var dbga: std.heap.DebugAllocator(.{}) = .init;
    defer {
        _ = dbga.detectLeaks();
        assert(.ok == dbga.deinit());
    }
    const allocator = dbga.allocator();
    action_allocator = ActionAllocator.init(std.heap.page_allocator);
    defer action_allocator.reset();
    ConfigList_init(allocator, .init(std.heap.page_allocator));
    defer cfgl.pool.reset();
    cfgl.allocator = allocator;

    std.debug.print("lemon for great justice!\n", .{});
    std.process.exit(0);
}

test "exe mentioned" {
    std.debug.print("hello from lemon main\n", .{});
}
