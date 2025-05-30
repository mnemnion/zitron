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

const assert = std.debug.assert;

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
    type: SymbolType,
    /// Linked list of rules of this (if an NT)
    rule: ?*Rule,
    /// fallback token in case this token doesn't parse
    fallback: ?*Symbol,
    /// Precedence if defined (-1 otherwise)
    prec: int, // Should be ?u16 probably
    /// Associativity if precedence is defined
    assoc: E_Assoc,
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
    precsym: *Symbol,
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
    nextlhs: *Rule,
    /// Next rule in the global list
    next: *Rule,
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
    // TODO: Fill in the rest of these, I am fatigued
    symbols: []*Symbol,

    errorcnt: int,
    errsym: *Symbol,
    wildcard: *Symbol,
    name: []u8,
    arg: []u8,
    tokentype: []u8,
    vartype: []u8,
    start: []u8,
    stacksize: []u8,
    include: []u8,
    @"error": []u8,
    overflow: []u8,
    failure: []u8,
    accept: []u8,
    extracode: []u8,
    tokendest: []u8,
    vardest: []u8,
    filename: []u8,
    outname: []u8,
    tokenprefix: []u8,

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
    cfp.model = dot;
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
    cfp.model = dot;
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
