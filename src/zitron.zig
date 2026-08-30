//! Zitron: A LALR(1) Parser Generator for Zig
//!
//! Zitron is a parser generator for Zig, based on D. Richard Hipp's
//! Lemon.
//!
//! The author and translator of this program disclaim copyright.
//!
//!  In place of a legal notice, here is a blessing:
//!
//!    May you do good and not evil.
//!    May you find forgiveness for yourself and forgive others.
//!    May you share freely, never taking more than you give.
//!

const std = @import("std");
const builtin = @import("builtin");
const config = @import("config");
const mem = std.mem;
const Allocator = mem.Allocator;
const ArrayHashMap = std.ArrayHashMapUnmanaged;
const MemoryPool = std.heap.memory_pool.Managed;
const ArrayList = std.ArrayListUnmanaged;
const StringArrayHashMap = std.StringArrayHashMapUnmanaged;
const AllocatingWriter = std.Io.Writer.Allocating;
const File = std.Io.File;

const OOM = Allocator.Error;

const isLower = std.ascii.isLower;
const isUpper = std.ascii.isUpper;
const isAlnum = std.ascii.isAlphanumeric;
const isAlpha = std.ascii.isAlphabetic;
const isSpace = std.ascii.isWhitespace;

const sort = std.mem.sort;

const assert = std.debug.assert;

const exit = std.process.exit;

const logger = std.log.scoped(.lemon);

const is_debug = builtin.mode == .Debug;
const is_safe = is_debug or builtin.mode == .ReleaseSafe;

fn dbgassert(ok: bool) void {
    if (is_debug) {
        assert(ok);
    }
}

const dprint = std.debug.print;

//| NOTE: these should become build flags

const do_not_optimize_terminals = true;
const print_aliases = false;
const print_code = false;

//| Useful Constants

const C_SPACE = " \t\n\r\x0b\x0c"; // C locale definition of isspace(3)

// Various print control variables

/// Prints which are already passing
const p_check1 = false;
/// Failing prints which I don't want to see
const p_check2 = false;
/// Prints I'm trying to get to pass
const p_check_this = false;
/// Possibly-useful prints which are ahead of the curve
const p_check_next = false;
/// Check the preprocessor.
const p_pp = false;

const p_debug = false;

const p_print = false;
const p_errcnt = true;
const p_symbols = false;
const p_statefind = false;

// NOTE: This is not, in fact, how strcmp works.  If it turns out
// I need anything other than != 0 and == 0 from strcmp, which I doubt,
// I can decide how to handle that then.

fn strcmp(a: []const u8, b: []const u8) bool {
    if (a.len == 0 and b.len == 0) return false;
    return std.mem.eql(u8, a, b);
}

//| Casting
//|
//| Various essential shorthands for getting Zig to play ball.

inline fn cast(T: type, val: anytype) T {
    return @as(T, @intCast(val));
}

inline fn uint(i: anytype) @Int(.unsigned, @typeInfo(@TypeOf(i)).int.bits) {
    if (@typeInfo(@TypeOf(i)).int.signedness == .unsigned) {
        @compileError("Value is already an unsigned type");
    }
    return @intCast(i);
}

inline fn sint(i: anytype) @Int(.signed, @typeInfo(@TypeOf(i)).int.bits + 1) {
    if (@typeInfo(@TypeOf(i)).int.signedness == .signed) {
        @compileError("Value is already a signed type");
    }
    return @intCast(i);
}

// Definition of `int`.  This should help me figure out which should
// be unsigned, optional, or both, and which should in fact be an
// i32 (if any).  All type references to `int` should disappear.

const int = i32;

// Originally this was:
// const MAXRHS = if (builtin.is_test) 5 else 1000;
// which strikes me as too low and is definitely too high.
// So now we do:
const MAXRHS = 128;
// So that the `i8` in the template for `yyRuleInfoNRhs` cashes out.

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
    /// Symbols are one of .terminal, .nonterminal, or .multiterminal.
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
    useCnt: u32,
    /// Code which executes whenever this symbol is
    /// popped from the stack during error processing
    destructor: []u8,
    /// Line number for start of destructor.  This is
    /// `0` if a line has not been set, positive if it
    /// has, and `null` to deduplicate destructors.
    destLineno: ?u32,
    /// The data type of information held by this
    /// object. Only used if type==NONTERMINAL
    datatype: []u8,
    /// The data type tag.  In the parser, the value
    /// stack is a union.  This string is used in `.@"{s}"`
    /// form to access the correct datatype.  Will have the
    /// same contents (modulo whitespace) as `datatype` when
    /// the latter isn't "".
    dttag: []const u8,
    /// The data type number.  A hash of `dttag`, this was
    /// originally used to generate the field access, and is
    /// retained for easy type-comparison.  For tokens, this
    /// is 0, rather than the hash of %token_type.
    dtnum: u32,
    /// True if this symbol ever carries content - if
    /// it is ever more than just syntax
    bContent: bool,
    // following fields are used by MULTITERMINALs only
    /// Array (slice) of constituent symbols
    subsym: []*Symbol,

    pub const empty: Symbol = .{
        .name = "UNIN!TIALIZED",
        .index = 0,
        .type = .nonterminal,
        .rule = null,
        .fallback = null,
        .prec = null,
        .assoc = .unk,
        .lambda = false,
        .firstset = undefined,
        .useCnt = 0,
        .destructor = undefined,
        .destLineno = 0,
        .datatype = undefined,
        .dttag = "",
        .dtnum = 0,
        .bContent = false,
        .subsym = undefined,
    };

    // Valid, if dodgy, mutable Symbol pointer target,
    // used to initialize ParserState to a non-undefined
    // value.
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
        // The []const u8 fields are interned or static,
        // thus handled elsewhere.
        allocator.free(sp.firstset);
        allocator.free(sp.destructor);
        allocator.free(sp.datatype);
        allocator.free(sp.subsym);
        allocator.destroy(sp);
    }
};

const ImplSafe = struct {
    allocator: Allocator,
    impls: StringArrayHashMap(*Impl),

    pub fn init(allocator: Allocator) ImplSafe {
        is_impl_safe = true;
        return .{ .allocator = allocator, .impls = .empty };
    }

    pub fn deinit(impls: *ImplSafe) void {
        defer is_impl_safe = false;
        for (impls.impls.values()) |impl| {
            impls.allocator.free(impl.rhsalias);
            impls.allocator.free(impl.code);
            impls.allocator.destroy(impl);
        }
        impls.impls.deinit(impls.allocator);
    }

    pub fn get(impls: *ImplSafe, name: []const u8) !*Impl {
        dbgassert(is_impl_safe);
        if (impls.impls.get(name)) |impl| {
            return impl;
        }
        const impl = try impls.allocator.create(Impl);
        impl.* = .empty;
        impl.name = name;
        impl.rhsalias = try impls.allocator.alloc([]const u8, 0);
        impl.code = try impls.allocator.alloc(u8, 0);
        try impls.impls.put(impls.allocator, name, impl);
        return impl;
    }
};

threadlocal var impl_safe: ImplSafe = undefined;
threadlocal var is_impl_safe: bool = false;

/// An Impl is named code, rather than literal code which
/// is listed directly after the rule.
const Impl = struct {
    name: []const u8,
    rule: ?*Rule,
    code: []u8,
    line: usize,
    lhsalias: []const u8,
    rhsalias: [][]const u8,

    pub const empty: Impl = .{
        .name = "",
        .rule = null,
        .code = &.{},
        .line = 0,
        .lhsalias = "",
        .rhsalias = &.{},
    };
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

fn nextNamedAliasIndex(aliases: []const []const u8, start: usize) ?usize {
    if (start >= aliases.len) return null;
    for (aliases[start..], start..) |alias, i| {
        if (alias.len > 0) return i;
    }
    return null;
}

fn rhsAliasesHaveNames(aliases: []const []const u8) bool {
    return nextNamedAliasIndex(aliases, 0) != null;
}

const RhsAliasComparison = union(enum) {
    match,
    extra_impl,
    differing: struct {
        impl_alias: []const u8,
        rule_alias: []const u8,
    },
    missing_rule: []const u8,
};

fn compareRhsAliasNames(impl_aliases: []const []const u8, rule_aliases: []const []const u8) RhsAliasComparison {
    var rule_idx: usize = 0;
    for (impl_aliases) |impl_alias| {
        dbgassert(impl_alias.len > 0);
        const next_idx = nextNamedAliasIndex(rule_aliases, rule_idx) orelse return .extra_impl;
        const rule_alias = rule_aliases[next_idx];
        if (!mem.eql(u8, impl_alias, rule_alias)) {
            return .{ .differing = .{
                .impl_alias = impl_alias,
                .rule_alias = rule_alias,
            } };
        }
        rule_idx = next_idx + 1;
    }
    if (nextNamedAliasIndex(rule_aliases, rule_idx)) |idx| {
        return .{ .missing_rule = rule_aliases[idx] };
    }
    return .match;
}

fn ruleHasAliases(rule: *const Rule) bool {
    if (rule.lhsalias.len > 0) return true;
    return rhsAliasesHaveNames(rule.rhsalias);
}

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
/// It is not currently in use, but it would be a good idea
/// to go back later and make `action.x` into a tagged union,
/// instead of a bare union with a separated type tag.  Too
/// much deviation from the source for now.
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
    type: E_Action = ._not_initialized,
    x: union {
        stp: *State,
        rp: ?*Rule,
    } = undefined,
    /// SHIFTREDUCE optimization to this symbol
    spOpt: ?*Symbol = null,
    /// Next action for this state
    next: ?*Action = null,
    /// Tie-breaker in sorting
    age: usize,

    // [490]
    pub fn new() !*Action {
        const act = try action_allocator.create();
        act.* = .{ .age = action_age };
        action_age += 1;
        return act;
    }

    //| NOTE: these two were originally one method, but I'm not in the mood to do
    //| the casting and other paperwork to get Zig to cooperate with that.  All of
    //| this code should get refactored later to change how that all works, but
    //| I'm out of budget to make on-the-fly changes as I get to the hairiest part
    //| of the original.

    pub fn addState(app: *?*Action, e_type: E_Action, sp: *Symbol, stp: *State) !void {
        const newaction = try Action.new();
        newaction.next = app.*;
        app.* = newaction;
        newaction.type = e_type;
        newaction.sp = sp;
        // newaction.spOpt = null;
        newaction.x = .{ .stp = stp };
    }

    pub fn addRule(app: *?*Action, e_type: E_Action, sp: *Symbol, rp: ?*Rule) !void {
        const newaction = try Action.new();
        newaction.next = app.*;
        app.* = newaction;
        newaction.type = e_type;
        newaction.sp = sp;
        // newaction.spOpt = null;
        newaction.x = .{ .rp = rp };
    }

    pub const sort = mergeSortFn(Action, "next", actioncmp);

    // Compare two actions.  Return `true` if the first is less than
    // or equal to the second, `false` otherwise.
    fn actioncmp(ap1: *Action, ap2: *Action) bool {
        if (ap1.sp.index < ap2.sp.index) return true;
        if (ap1.sp.index > ap2.sp.index) return false;
        if (@intFromEnum(ap1.type) < @intFromEnum(ap2.type)) return true;
        if (@intFromEnum(ap1.type) > @intFromEnum(ap2.type)) return false;
        // ap2.x will cast identically because they have the same type:
        if (ap1.type == .reduce or ap1.type == .shiftreduce) {
            if (p_debug) dprint("ap1.type {s} ap2.type {s}\n", .{ @tagName(ap1.type), @tagName(ap2.type) });
            if (ap1.x.rp.?.index < ap2.x.rp.?.index) return true;
            if (ap1.x.rp.?.index > ap2.x.rp.?.index) return false;
        }
        {
            // otherwise... raw pointer comparison??
            // Turns up in the SQLite parser, but this works too:
            return ap1.age < ap2.age;
            // This is the order they're subtracted in the original:
            // return (@intFromPtr(ap2) < @intFromPtr(ap1));
        }
    }
};

/// Each state of the generated parser's finite state machine
/// is encoded as an instance of the following structure.
const State = struct {
    /// The basis configurations for this state
    bp: ?*Config = null,
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
    iTknOfst: int,
    /// yy_action[] offset for nonterminals
    iNtOfst: int,
    /// Default action is to REDUCE by this rule
    iDfltReduce: int,
    /// The default REDUCE rule.
    pDefltReduce: ?*Rule,
    /// True if this is an auto-reduce state
    autoreduce: bool,

    pub const empty: State = .{
        .statenum = 0,
        .ap = null,
        .nTknAct = 0,
        .nNtAct = 0,
        .iTknOfst = 0,
        .iNtOfst = 0,
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
            h = h *% 571 +% a.rp.index *% 37 +% a.dot;
            next_cfg = a.bp;
        }
        return h;
    }

    pub fn eql(_: StateContext, a_cfg: *Config, b_cfg: *Config, _: usize) bool {
        var rc: i32 = 0;
        var a: ?*Config = a_cfg;
        var b: ?*Config = b_cfg;
        while (rc == 0 and a != null and b != null) {
            const a1: *Config = a.?;
            const b1: *Config = b.?;
            rc = cast(i32, a1.rp.index) - cast(i32, b1.rp.index);
            if (rc == 0) rc = cast(i32, a1.dot) - cast(i32, b1.dot);
            a = a1.bp;
            b = b1.bp;
        }
        if (rc == 0) {
            if (a) |_| rc = 1;
            if (b) |_| rc = -1;
        }
        return (rc == 0);
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
    if (p_statefind) {
        dprint("Looking for {s}:{d}-{d}\n", .{ bp.rp.lhs.name, bp.rp.index, bp.dot });
    }
    const maybe_sp = state_map.safe.get(bp);
    if (maybe_sp) |_| {
        if (p_statefind) dprint("  Found\n", .{});
    } else {
        if (p_statefind) dprint("  Not found\n", .{});
    }
    return maybe_sp;
}

fn State_insert(data: *State, key: *Config) !bool {
    dbgassert(is_state_map);
    if (p_statefind) dprint("Inserting {s}:{d}-{d}\n", .{ key.rp.lhs.name, key.rp.index, key.dot });
    if (state_map.safe.getKey(key)) |_| return false;
    if (p_statefind) dprint("  Inserted\n", .{});
    try state_map.safe.put(state_map.allocator, key, data);
    return true;
}

/// Returns the values array of all states.  Nothing is allowed to
/// use the state map after this is called.
fn State_arrayof() []*State {
    return state_map.safe.values();
}

fn State_free() void {
    for (state_map.safe.values()) |st| {
        Configlist_freesets(st.cfp, state_map.allocator);
        Configlist_freesets(st.bp, state_map.allocator);
        state_map.allocator.destroy(st);
    }
    state_map.safe.deinit(state_map.allocator);
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

fn Plink_deinit() void {
    plink_freelist.deinit();
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

// /*********************** From the file "report.c" **************************/
// /*
// ** Procedures for generating reports and tables in the LEMON parser generator.
// */

/// Generate a filename with the given suffix.  Space to hold the
/// name comes from malloc() and must be freed by the calling
/// function.  Quote outname for line directives, and assign the
/// filenames to the correct fields of `lemp`.
fn assign_outname(zyt: *Zitron, suffix: []const u8, escape: bool) OOM!void {
    if (zyt.outname.len > 0) zyt.allocator.free(zyt.outname);
    zyt.outname = try file_makename(zyt, suffix);
    check_filename(zyt.outname) catch |err| {
        if (zyt.linenosflag) {
            switch (err) {
                error.FileNameHasNewline => {
                    dprint("Filename has newline, line numbers cannot be printed\n", .{});
                },
                error.FileNameHasTab => {
                    dprint("Filename has tab, line numbers cannot be printed\n", .{});
                },
                error.FileNameNotUtf8 => {
                    dprint("Filename is not valid UTF-8, line numbers cannot be printed\n", .{});
                },
            }
            zyt.errorcnt += 1;
        }
    };
    if (escape) zyt.outname = zyt.outname;
}

fn file_makename(zyt: *Zitron, suffix: []const u8) OOM![]const u8 {
    var buf: AllocatingWriter = .init(zyt.allocator);
    errdefer buf.deinit();

    const w = &buf.writer;
    var filename = if (zyt.opt.output_file.len > 0) zyt.opt.output_file else zyt.filename;

    if (zyt.opt.output_directory.len > 0) {
        const dir = zyt.opt.output_directory;
        if (std.mem.lastIndexOfScalar(u8, filename, '/')) |i| {
            filename = filename[i + 1 ..];
        }
        w.print("{s}/", .{dir}) catch return error.OutOfMemory;
    }

    if (std.mem.lastIndexOfScalar(u8, filename, '.')) |dot| {
        filename = filename[0..dot];
    }

    w.print("{s}{s}", .{ filename, suffix }) catch return error.OutOfMemory;

    return buf.toOwnedSlice();
}

/// Open a file with a name based on the name of the input file,
/// but with a different (specified) suffix, and return a pointer
/// to the stream.
fn file_open(zyt: *Zitron, suffix: []const u8, escape: bool, mode: File.CreateFlags) OOM!?File {
    try assign_outname(zyt, suffix, escape);
    const fh = open_file(zyt, zyt.outname, mode);
    return fh;
}

fn open_file(zyt: *Zitron, name: []const u8, mode: File.CreateFlags) OOM!?File {
    return std.Io.Dir.cwd().createFile(zyt.io, name, mode) catch |err| {
        zyt.errorcnt += 1;
        switch (err) {
            error.IsDir => {
                logger.err("file open error: path is a directory '{s}'\n", .{zyt.outname});
                return null;
            },
            error.FileNotFound => {
                logger.err("file open error: file not found '{s}'\n", .{zyt.outname});
                return null;
            },
            error.AccessDenied => {
                logger.err("file open error: permission denied '{s}'\n", .{zyt.outname});
                return null;
            },
            else => |e| {
                logger.err("file open error: unexpected error {s} opening '{s}'\n", .{ @errorName(e), zyt.outname });
                return null;
            },
        }
    };
}

/// Print the text of a rule
fn rule_print(writer: anytype, rp: *Rule) !void {
    try writer.print("{s}", .{rp.lhs.name});
    if (comptime print_aliases) {
        if (rp.lhsalias.len > 0) try writer.print("({s})", .{rp.lhsalias});
    }
    try writer.writeAll(" ::=");
    for (rp.rhs, rp.rhsalias) |sp, alias| {
        if (sp.type == .multiterminal) {
            try writer.print(" {s}", .{sp.subsym[0].name});
            for (sp.subsym[1..]) |ssp| {
                try writer.print("|{s}", .{ssp.name});
            }
        } else {
            try writer.print(" {s}", .{sp.name});
        }
        if (comptime print_aliases) {
            if (alias.len > 0) try writer.print("({s})", .{alias});
        }
    }
}

/// Duplicate the input file without comments and without actions
/// on rules
fn Reprint(zyt: *Zitron) !void {
    var stdout_buffer: [4096]u8 = undefined;
    var stdout_writer = std.Io.File.stdout().writer(zyt.io, &stdout_buffer);
    const out = &stdout_writer.interface;
    try out.print("// Reprint of input file {s}.\n// Symbols:\n", .{zyt.filename});
    var maxlen: usize = 10;
    for (zyt.symbols[0..zyt.nsymbol]) |sp| {
        const len = sp.name.len;
        if (len > maxlen) maxlen = len;
    }
    const ncolumns = @max(1, 76 / (maxlen + 5));
    const skip = (zyt.nsymbol + ncolumns - 1) / ncolumns;
    for (0..skip) |i| {
        try out.writeAll("//");
        var j: usize = i;
        while (j < zyt.nsymbol) : (j += skip) {
            const sp = zyt.symbols[j];
            dbgassert(sp.index == j);
            const ptsym = if (maxlen < sp.name.len) sp.name[0..maxlen] else sp.name;
            try out.print(" {d: >3} ", .{j});
            try out.print("{s}", .{ptsym});
            if (ptsym.len < maxlen) {
                try out.splatByteAll(' ', maxlen - ptsym.len);
            }
            try out.writeByte('\n');
        }
    }
    var m_rp: ?*Rule = zyt.rule;
    while (m_rp) |rp| : (m_rp = rp.next) {
        try rule_print(out, rp);
        try out.writeByte('.');
        if (rp.precsym) |precsym| try out.print(" [{s}]", .{precsym.name});
        if (comptime print_code) if (rp.code) try out.print("\n    {s}", .{rp.code});
        try out.writeByte('\n');
    }
    try out.flush();
}

/// Print a single rule.
fn RulePrint(writer: anytype, rp: *Rule, iCursor: ?usize) !void {
    try writer.print("{s} ::=", .{rp.lhs.name});
    for (0..rp.rhs.len + 1) |i| {
        if (i == iCursor) try writer.writeAll(" *");
        if (i == rp.rhs.len) break;
        const sp = rp.rhs[i];
        if (sp.type == .multiterminal) {
            try writer.print(" {s}", .{sp.subsym[0].name});
            for (sp.subsym[1..]) |ssp| {
                try writer.print("|{s}", .{ssp.name});
            }
        } else {
            try writer.print(" {s}", .{sp.name});
        }
    }
}

/// Print the rule for a configuration.
fn ConfigPrint(writer: anytype, cfp: *Config) !void {
    try RulePrint(writer, cfp.rp, cfp.dot);
}

// TODO: SetPrint goes here
// TODO: PlinkPrint goes here

// Print an action to the given file descriptor.  Return FALSE if
// nothing was actually printed.
fn PrintAction(
    writer: anytype,
    ap: *Action,
    indent: usize,
    showPrecendenceConflict: bool,
) !bool {
    var printed = true;
    switch (ap.type) {
        .shift => {
            try writer.print("{[name]s: >[width]} shift        {[st]d: <7}", .{
                .name = ap.sp.name,
                .width = indent,
                .st = ap.x.stp.statenum,
            });
        },
        .reduce => {
            try writer.print("{[name]s: >[width]} reduce       {[st]d: <7}", .{
                .name = ap.sp.name,
                .width = indent,
                .st = ap.x.rp.?.iRule,
            });
            try RulePrint(writer, ap.x.rp.?, null);
        },
        .shiftreduce => {
            try writer.print("{[name]s: >[width]} shift-reduce {[st]d: <7}", .{
                .name = ap.sp.name,
                .width = indent,
                .st = ap.x.rp.?.iRule,
            });
            try RulePrint(writer, ap.x.rp.?, null);
        },
        .accept => {
            try writer.print("{[name]s: >[width]} accept", .{
                .name = ap.sp.name,
                .width = indent,
            });
        },
        .@"error" => {
            try writer.print("{[name]s: >[width]} error", .{
                .name = ap.sp.name,
                .width = indent,
            });
        },
        .rrconflict, .srconflict => {
            try writer.print("{[name]s: >[width]} reduce       {[st]d: <7} ** Parsing conflict **", .{
                .name = ap.sp.name,
                .width = indent,
                .st = ap.x.rp.?.iRule,
            });
        },
        .ssconflict => {
            try writer.print("{[name]s: >[width]} shift        {[st]d: <7} ** Parsing conflict **", .{
                .name = ap.sp.name,
                .width = indent,
                .st = ap.x.stp.statenum,
            });
        },
        .sh_resolved => {
            if (showPrecendenceConflict) {
                try writer.print("{[name]s: >[width]} shift        {[st]d: <7} -- dropped by precedence", .{
                    .name = ap.sp.name,
                    .width = indent,
                    .st = ap.x.stp.statenum,
                });
            } else {
                printed = false;
            }
        },
        .rd_resolved => {
            if (showPrecendenceConflict) {
                try writer.print(
                    "{[name]s: >[width]} reduce       {[st]d: <7} -- dropped by precedence",
                    .{
                        .name = ap.sp.name,
                        .width = indent,
                        .st = ap.x.rp.?.iRule,
                    },
                );
            } else {
                printed = false;
            }
        },
        .not_used => {
            printed = false;
        },
        ._not_initialized => unreachable,
    }
    if (printed) {
        if (ap.spOpt) |spOpt| {
            try writer.print("  /* because {s}=={s} */", .{ ap.sp.name, spOpt.name });
        }
    }
    return printed;
}

/// Generate the "*.out" log file
fn ReportOutput(zyt: *Zitron) !void {
    const m_fh = try file_open(zyt, ".out", false, .{});
    if (m_fh) |fh| {
        defer fh.close(zyt.io);
        var out_buffer: [4096]u8 = undefined;
        var f_writer = fh.writer(zyt.io, &out_buffer);
        const out = &f_writer.interface;
        try reportOutputImpl(zyt, out);
        try out.flush();
    } else {
        return; // No file handle
    }
}

/// Write the report to the provided writer.
fn reportOutputImpl(zyt: *Zitron, writer: anytype) !void {
    for (0..zyt.nxstate) |i| {
        const stp = zyt.sorted[i];
        try writer.print("State {d}:\n", .{stp.statenum});
        var m_cfp: ?*Config = if (!zyt.opt.only_basis) stp.cfp else stp.bp;
        while (m_cfp) |cfp| {
            var buf: [20]u8 = .{0} ** 20;
            if (cfp.dot == cfp.rp.rhs.len) {
                const dot_s = try std.fmt.bufPrint(&buf, "({d})", .{cfp.rp.iRule});
                try writer.print("    {s:>5} ", .{dot_s});
            } else {
                try writer.splatByteAll(' ', 10);
            }
            try ConfigPrint(writer, cfp);
            try writer.writeByte('\n');
            if (!zyt.opt.only_basis) {
                m_cfp = cfp.next;
            } else {
                m_cfp = cfp.bp;
            }
        }
        try writer.writeByte('\n');
        var m_ap = stp.ap;
        while (m_ap) |ap| : (m_ap = ap.next) {
            if (try PrintAction(writer, ap, 30, zyt.opt.show_conflicts)) try writer.writeByte('\n');
        }
        try writer.writeByte('\n');
    }
    try writer.writeAll("----------------------------------------------------\n");
    try writer.writeAll("Symbols:\n");
    try writer.writeAll("The first-set of non-terminals is shown after the name.\n\n");
    for (zyt.symbols[0..zyt.nsymbol], 0..) |sp, i| {
        try writer.print("  {d:>3}: {s}", .{ i, sp.name });
        if (sp.type == .nonterminal) {
            try writer.writeByte(':');
            if (sp.lambda) {
                try writer.writeAll(" <lambda>");
            }
            for (0..zyt.nterminal) |j| {
                if (sp.firstset.len > 0 and sp.firstset[j]) {
                    try writer.print(" {s}", .{zyt.symbols[j].name});
                }
            }
        }
        if (sp.prec) |prec| {
            try writer.print(" (precedence={d})", .{prec});
            if (sp.assoc != .unk) try writer.print(" (assoc={t})", .{sp.assoc});
        }
        try writer.writeByte('\n');
    }
    try writer.writeAll("----------------------------------------------------\n");
    try writer.writeAll("Syntax-only Symbols:\n");
    try writer.writeAll("The following symbols never carry semantic content.\n\n");
    {
        var n: usize = 0;
        for (0..zyt.nsymbol) |i| {
            const sp = zyt.symbols[i];
            if (sp.bContent) continue;
            const w = sp.name.len;
            if (n > 0 and n + w > 75) {
                try writer.writeByte('\n');
                n = 0;
            }
            if (n > 0) {
                try writer.writeByte(' ');
                n += 1;
            }
            try writer.print("{s}", .{sp.name});
            n += w;
        }
        if (n > 0) try writer.writeByte('\n');
    }
    try writer.writeAll("----------------------------------------------------\n");
    try writer.writeAll("Rules:\n");
    {
        var m_rp: ?*Rule = zyt.rule;
        while (m_rp) |rp| : (m_rp = rp.next) {
            try writer.print("{d:>4}: ", .{rp.iRule});
            try rule_print(writer, rp);
            try writer.writeByte('.');
            if (rp.precsym) |precsym| {
                try writer.print(" [{s} precedence={d}]", .{ precsym.name, precsym.prec.? });
            }
            try writer.writeByte('\n');
        }
    }
}

/// Write the contents of `str` to `out`, indenting by `ident` spaces.
/// The write always ends with  `\n`.  Returns `true` if it wrote a
/// newline not present in the original.
fn writeToIndent(out: anytype, str: []const u8, ident: usize) !bool {
    if (str.len == 0) return false;
    try out.splatByteAll(' ', ident);
    var start: usize = 0;
    while (start < str.len and (str[start] == ' ' or str[start] == '\t')) : (start += 1) {}
    if (start == str.len) return false; // ?? ¯\_(ツ)_/¯
    while (std.mem.indexOfScalarPos(u8, str, start, '\n')) |i| {
        const next = @min(i + 1, str.len);
        try out.writeAll(str[start..next]);
        start = next;
        while (start < str.len and (str[start] == ' ' or str[start] == '\t')) : (start += 1) {}
        if (start < str.len) try out.splatByteAll(' ', ident);
    }
    while (start < str.len and (str[start] == ' ' or str[start] == '\t')) : (start += 1) {}
    try out.writeAll(str[start..]);
    if (str[str.len - 1] != '\n') {
        try out.writeByte('\n');
        return true;
    } else {
        return false;
    }
}

/// Emulates `fgets` close enough for our purposes:
/// each call to `next` returns a line, with its newline
/// when there is one, and advances the pointer to the
/// template.
const Fgets = struct {
    in: *[:0]const u8,

    pub fn next(gets: *Fgets) ?[]const u8 {
        if (gets.in.*[0] == '\x00') return null;
        const m_nl = mem.indexOfScalar(u8, gets.in.*, '\n');
        if (m_nl) |nl| {
            defer gets.in.* = gets.in.*[nl + 1 .. :0];
            return gets.in.*[0 .. nl + 1];
        } else {
            defer gets.in.* = gets.in.*[gets.in.*.len..gets.in.*.len :0];
            return gets.in.*[0..gets.in.*.len];
        }
    }
};

fn fgets(in: *[:0]const u8) Fgets {
    return .{ .in = in };
}

//| [3549]
//|
//| The next cluster of routines are for reading the template file
//| and writing the results to the generated parser.

/// The first function transfers data from "in" to "out" until
/// a line is seen which begins with "%%".  The line number is
/// tracked.
///
/// if name!=0, then any word that begin with "Parse" is changed to
/// begin with *name instead.
fn tplt_xfer(name: []const u8, in: *[:0]const u8, out: anytype, lineno: *usize) !void {
    var start: usize = 0;
    var iter = fgets(in);
    while (iter.next()) |line| {
        start += line.len + 1;
        if (line.len < 2 or (line[0] != '%' and line[1] != '%')) {
            lineno.* += 1;
            var i: usize = 0;
            if (name.len > 0) {
                scan: while (mem.indexOfPos(u8, line, i, "Parse")) |p_idx| {
                    if (p_idx != 0 and isAlpha(line[p_idx - 1])) {
                        try out.writeAll(line[i .. p_idx + 5]);
                        i = p_idx + 5;
                        continue :scan;
                    }
                    try out.print("{s}{s}", .{ line[i..p_idx], name });
                    i = p_idx + 5;
                }
            }
            try out.writeAll(line[i..]);
        } else {
            break;
        }
    }
}

/// Skip forward past the header of the template file to the first "%%".
fn tplt_skip_header(in: *[:0]const u8) void {
    const h_idx = mem.indexOf(u8, in.*, "\n%%");
    if (h_idx) |i| {
        in.* = in.*[i + 4 ..];
    } else {
        logger.err("Header of template file: /^%%/ not found", .{});
        return; // TODO: something better? just die?
    }
}

// The next function finds the template file and opens it, returning
// a pointer to the opened file.

/// Retrieve the template.  First item of the tuple is `true` if the
/// second must be freed.
fn tplt_open(zyt: *Zitron) !struct { bool, [:0]const u8 } {
    if (zyt.opt.user_templatename.len > 0) {
        const file = if (std.Io.Dir.cwd().openFile(zyt.io, zyt.opt.user_templatename, .{})) |f| file: {
            break :file f;
        } else |err| {
            std.debug.print("Template file open error {s}", .{@errorName(err)});
            exit(@truncate(@intFromError(err)));
        };
        defer file.close(zyt.io);
        const end_pos = (try file.stat(zyt.io)).size;
        const filebuf = try zyt.allocator.allocSentinel(u8, end_pos, 0);
        defer zyt.allocator.free(filebuf);
        const read_bytes = try file.readPositionalAll(zyt.io, filebuf, 0);
        if (read_bytes < end_pos) {
            std.debug.print(
                "Didnt read to end of file {s}\n",
                .{zyt.opt.user_templatename},
            );
            std.process.exit(1);
        }
        return .{ true, filebuf };
    }
    const z_template = @embedFile("z_template");
    return .{ false, z_template };
}

/// Print a `// #line` comment to the output file.
fn tplt_linedir(out: anytype, lineno: usize, quoted_filename: []const u8) !void {
    try out.print("// #line {d} {s}\n", .{ lineno, quoted_filename });
}

/// Print a string to the file and keep the linenumber up to date.
fn tplt_print(out: anytype, zyt: *Zitron, str: []const u8, lineno: *usize) !void {
    if (str.len == 0) return;
    const line_count = mem.count(u8, str, "\n");
    lineno.* += line_count;
    try out.writeAll(str);
    if (str[str.len - 1] != '\n') {
        try out.writeByte('\n');
        lineno.* += 1;
    }
    if (zyt.linenosflag) {
        lineno.* += 1;
        try tplt_linedir(out, lineno.*, zyt.outname);
    }
}

//
// The following routine emits code for the destructor for the
// symbol sp
//
fn emit_destructor_code(out: anytype, sp: *Symbol, zyt: *Zitron, lineno: *usize) !void {
    const cp = cp: {
        if (sp.type == .terminal) {
            if (zyt.tokendest.len == 0) return;
            try out.writeAll("        => {\n");
            lineno.* += 1;
            break :cp zyt.tokendest;
        } else if (sp.destructor.len > 0) {
            try out.writeAll("        => {\n");
            lineno.* += 1;
            if (zyt.linenosflag) {
                lineno.* += 1;
                try tplt_linedir(out, sp.destLineno.?, zyt.filename);
            }
            break :cp sp.destructor;
        } else if (zyt.vardest.len > 0) {
            try out.writeAll("        => {\n");
            lineno.* += 1;
            break :cp zyt.vardest;
        } else {
            unreachable;
        }
    };
    // TODO: We could indent this. I guess...
    var cursor: usize = 0;
    lineno.* += mem.count(u8, cp, "\n");
    while (mem.indexOfPos(u8, cp, cursor, "$$")) |i| {
        try out.writeAll(cp[cursor..i]);
        try out.print("(yypminor.@\"{s}\")", .{sp.dttag});
        cursor = i + 2;
    }
    try out.writeAll(cp[cursor..]);
    try out.writeByte('\n');
    lineno.* += 1;
    if (zyt.linenosflag) {
        lineno.* += 1;
        try tplt_linedir(out, lineno.* + 1, zyt.outname);
    }
    try out.writeAll("        },\n");
    lineno.* += 1;
    return;
}

/// Return TRUE (non-zero) if the given symbol has a destructor.
///
fn has_destructor(sp: *Symbol, zyt: *Zitron) bool {
    if (sp.type != .nonterminal) {
        return zyt.tokendest.len > 0;
    } else {
        return zyt.vardest.len > 0 or sp.destructor.len > 0;
    }
}

/// We want to track if an alias is use, but also if
/// it's been captured.  This lets us emit a destructor
/// if a token type is only captured by enum value.
const UseType = packed struct(u8) {
    used: bool,
    captured: bool,
    _: u6,

    pub const empty: UseType = @bitCast(@as(u8, 0));
};

/// Write and transform the rp->code string so that symbols are expanded.
/// Populate the rp->codePrefix and rp->codeSuffix strings, as appropriate.
///
/// Return `true` if the expanded code requires that "yylhsminor" local variable
/// to be defined.
fn translate_code(zyt: *Zitron, rp: *Rule) !bool {
    dbgassert(rp.rhs.len == rp.rhsalias.len);
    var rc = false; // True if yylhsminor is used
    var dontUseRhs0 = false; // If true, use of left-most RHS label is illegal
    var lhsused = false; // True if the LHS element has been used
    var lhsdirect = false; // True if LHS writes directly into stack
    var used: [MAXRHS]UseType = undefined; // True for each RHS element which is used
    var zLhsBuf: [64]u8 = undefined; // Convert the LHS symbol into this string
    var zSkip: ?usize = null; // Index of skippable special comment
    var zLhs: []const u8 = "";
    if (is_safe) {
        @memset(&used, UseType.empty);
    }
    const alloc = zyt.allocator;
    var fallback = std.heap.stackFallback(2048, alloc);
    const f_alloc = fallback.get();
    var string_builder: AllocatingWriter = .init(f_alloc);
    defer string_builder.deinit();
    const writer = &string_builder.writer;
    const cp = if (zyt.opt.linenos) rp.code else std.mem.trim(u8, rp.code, C_SPACE);
    if (cp.len == 0) {
        rp.code = "\n";
        rp.noCode = true;
    } else {
        rp.noCode = false;
    }
    if (rp.rhs.len == 0) {
        // If there are no RHS symbols, then writing directly to the LHS is ok
        lhsdirect = true;
    } else if (rp.rhsalias[0].len == 0) {
        // The left-most RHS symbol has no value.  LHS direct is ok.  But
        // we have to call the destructor on the RHS symbol first.
        lhsdirect = true;
        if (has_destructor(rp.rhs[0], zyt)) {
            if (p_check1) {
                dprint("destructor: {s} {d}\n", .{ rp.lhs.name, rp.iRule });
            }
            try writer.print(
                "yy_destructor(yypParser,{d},&(yymsp - {d})[1].minor);\n",
                .{ rp.rhs[0].index, rp.rhs.len },
            );
            alloc.free(rp.codePrefix);
            rp.codePrefix = try Strsafe(string_builder.writer.buffer[0..string_builder.writer.end]);
            string_builder.shrinkRetainingCapacity(0);
            rp.noCode = false;
        }
    } else if (rp.lhsalias.len == 0) {
        // There is no LHS value symbol.
        lhsdirect = true;
    } else if (strcmp(rp.lhsalias, rp.rhsalias[0])) {
        // The LHS symbol and the left-most RHS symbol are the same, so
        // direct writing is allowed
        lhsdirect = true;
        lhsused = true;
        used[0].used = true;
        used[0].captured = true;
        if (rp.lhs.dtnum != rp.rhs[0].dtnum) {
            ErrorMsg(zyt.filename, rp.ruleline, "" ++
                "{s}({s}) and {s}({s}) share the same label but have " ++
                "different datatypes: {s}: {s}, {s}: {s}", .{
                rp.lhs.name,
                rp.lhsalias,
                rp.rhs[0].name,
                rp.rhsalias[0],
                rp.lhs.name,
                rp.lhs.dttag,
                rp.rhs[0].name,
                rp.rhs[0].dttag,
            });
            zyt.errorcnt += 1;
        }
    } else {
        string_builder.shrinkRetainingCapacity(0);
        try writer.print("// {s}-overwrites-{s}\n", .{ rp.lhsalias, rp.rhsalias[0] });
        // `trimLeft` because we `trim` the code, so the index will be correct this way.
        // just `trim` can remove the newline, which we want to detect.
        if (mem.indexOf(u8, std.mem.trimStart(u8, rp.code, C_SPACE), string_builder.writer.buffer[0..string_builder.writer.end])) |skip_idx| {
            // The code contains a special comment that indicates that it is safe
            // for the LHS label to overwrite left-most RHS label.
            zSkip = skip_idx;
            lhsdirect = true;
        } else {
            lhsdirect = false;
        }
    }
    if (lhsdirect) {
        zLhs = std.fmt.bufPrint(&zLhsBuf, "(yymsp - {d})[1].minor.@\"{s}\"", .{
            rp.rhs.len,
            rp.lhs.dttag,
        }) catch unreachable;
    } else {
        rc = true;
        zLhs = std.fmt.bufPrint(
            &zLhsBuf,
            "yylhsminor.@\"{s}\"",
            .{rp.lhs.dttag},
        ) catch unreachable;
    }
    string_builder.shrinkRetainingCapacity(0);
    {
        // Build the translated code
        var i: usize = 0;
        var start: usize = 0;
        var special_start: usize, var special_end: usize = .{ 0, 0 };
        while (i < cp.len) : (i += 1) {
            // Handle comments
            if (cp[i] == '/' and i < cp.len - 1 and cp[i + 1] == '/') {
                // Special comment?
                if (i == zSkip) {
                    special_start = i;
                    i += 2;
                    while (i < cp.len and cp[i] != '\n') : (i += 1) {}
                    try writer.writeAll(cp[start..i]);
                    special_end = i;
                    start = i;
                    dontUseRhs0 = true;
                    continue;
                } else {
                    i += 2;
                    while (i < cp.len and cp[i] != '\n') : (i += 1) {}
                    continue;
                }
            }
            // Don't expand aliases inside strings either:
            if (cp[i] == '\\' and i < cp.len - 1 and cp[i + 1] == '\\') {
                // Skip multiline strings
                i += 2;
                while (i < cp.len and cp[i] != '\n') : (i += 1) {}
                continue;
            } else if (cp[i] == '"' or cp[i] == '\'') {
                // String or character literals (since the latter can have " in it)
                const startchar = cp[i];
                var prevc: u8 = 0;
                i += 1;
                while (i < cp.len and (cp[i] != startchar or prevc == '\\')) : (i += 1) {
                    if (cp[i] == '\n') {
                        ErrorMsg(zyt.filename, rp.ruleline, "" ++
                            "Zig code on this line contains an un-terminated string, or " ++
                            "botched character literal.", .{});
                        zyt.errorcnt += 1;
                        continue;
                    }
                    if (prevc == '\\')
                        prevc = 0
                    else
                        prevc = cp[i]; // clever
                }
                continue;
            }
            if ((isAlpha(cp[i]) or cp[i] == '@') and
                (i == 0 or (!isAlnum(cp[i - 1]) and cp[i] - 1 != '_')))
            {
                try writer.writeAll(cp[start..i]);
                start = i;
                const at = if (cp[i] == '@') true else false;
                if (at) i += 1;
                var id = i;
                // _valid_ zig code ends in `;` but we want to stay in bounds anyway:
                while (id < cp.len and isAlnum(cp[id]) or cp[id] == '_') : (id += 1) {}
                if (strcmp(rp.lhsalias, cp[i..id])) {
                    if (at) {
                        ErrorMsg(zyt.filename, rp.ruleline, "" ++
                            "It is invalid to @ the LHS alias: {s}", .{rp.code});
                        zyt.errorcnt += 1;
                    }
                    try writer.writeAll(zLhs);
                    lhsused = true;
                    i = id - 1; // Because we increment in the loop
                    start = id;
                } else rhs: for (rp.rhsalias, rp.rhs, 0..) |alias, rhs, j| {
                    if (alias.len > 0 and strcmp(alias, cp[i..id])) {
                        if (j == 0 and dontUseRhs0) {
                            ErrorMsg(zyt.filename, rp.ruleline, "" ++
                                "Alias {s} used after '{s}'.", .{
                                rp.rhsalias[0],
                                cp[special_start..special_end],
                            });
                            zyt.errorcnt += 1;
                        } else if (at) {
                            // If the argument is of the form @X then substitute
                            // the token enum of X, not the value of X
                            if (rp.rhs[j].type == .nonterminal) {
                                ErrorMsg(zyt.filename, rp.ruleline, "" ++
                                    "The @{s} conversion cannot be used on nonterminal {s}", .{
                                    rp.rhsalias[j],
                                    rp.rhs[j].name,
                                });
                            }
                            try writer.print(
                                "yyEnum((yymsp - {d})[1].major)",
                                .{rp.rhs.len - j},
                            );
                        } else {
                            // dontUseRhs0 has already been eliminated.
                            const dttag = if (rhs.type == .multiterminal)
                                rhs.subsym[0].dttag
                            else
                                rhs.dttag;
                            try writer.print(
                                "(yymsp - {d})[1].minor.@\"{s}\"",
                                .{ rp.rhs.len - j, dttag },
                            );
                        }
                        used[j].used = true;
                        if (!at) used[j].captured = true;
                        i = id - 1;
                        start = id;
                        break :rhs;
                    }
                }
            } // end alias substitution, if we did nothing i has not changed
        }
        try writer.writeAll(cp[start..]);
        // Main code generation completed
        // The previous value was also interned (in parseonetoken) so it's freed at the end:
        rp.code = try Strsafe(string_builder.writer.buffer[0..string_builder.writer.end]);
        string_builder.shrinkRetainingCapacity(0);
    }

    // Check to make sure the LHS has been used
    if (rp.lhsalias.len > 0 and !lhsused) {
        ErrorMsg(zyt.filename, rp.ruleline, "" ++
            "Label \"{s}\" for \"{s}({s})\" is never used.", .{
            rp.lhsalias,
            rp.lhs.name,
            rp.lhsalias,
        });
        zyt.errorcnt += 1;
    }

    // Generate destructor code for RHS minor values which are not referenced.
    // In modifying this code to generate Zig, it became clear that the throw-friendly
    // way to trigger end-state destructors is to `defer` them.  So we just write out
    // any `codePrefix` we already have, first:
    try writer.print("{s}", .{rp.codePrefix});
    // Generate error messages for unused labels and duplicate labels.
    for (rp.rhsalias, 0..rp.rhs.len) |alias, i| {
        if (alias.len > 0) {
            if (i > 0) {
                if (strcmp(rp.lhsalias, alias)) {
                    ErrorMsg(zyt.filename, rp.ruleline, "" ++
                        "{s}({s}) has the same label as the LHS ({s}) but is not the left-most " ++
                        "symbol on the RHS.", .{ rp.rhs[i].name, alias, rp.lhsalias });
                    zyt.errorcnt += 1;
                } // k-k-k-quadratic
                dupe: for (rp.rhsalias[0..i]) |alien| {
                    if (strcmp(alias, alien)) {
                        ErrorMsg(zyt.filename, rp.ruleline, "" ++
                            "Alias {s} used for multiple symbols on the RHS of a rule.", .{alias});
                        zyt.errorcnt += 1;
                    }
                    break :dupe;
                }
            }
            if (!used[i].used) {
                ErrorMsg(zyt.filename, rp.ruleline, "" ++
                    "Alias {s} for \"{s}({s})\" is never used.", .{ alias, rp.rhs[i].name, alias });
                zyt.errorcnt += 1;
            }
            if (!used[i].captured and has_destructor(rp.rhs[i], zyt)) {
                // Was @'ed upon but not otherwise touched. Destroy
                try writer.print(
                    "defer yy_destructor(yypParser,{d},&(yymsp - {d})[1].minor);\n",
                    .{ rp.rhs[i].index, rp.rhs.len - i },
                );
            }
        } else if (i > 0 and has_destructor(rp.rhs[i], zyt)) {
            if (p_check1) {
                dprint("destructor 2.0: {s} {d}\n", .{ rp.lhs.name, rp.iRule });
            }
            try writer.print(
                "defer yy_destructor(yypParser,{d},&(yymsp - {d})[1].minor);\n",
                .{ rp.rhs[i].index, rp.rhs.len - i },
            );
        }
    }
    rp.codePrefix = try Strsafe(string_builder.writer.buffer[0..string_builder.writer.end]);
    string_builder.shrinkRetainingCapacity(0);
    // If unable to write LHS values directly into the stack, write the
    // saved LHS value now.
    if (!lhsdirect) {
        try writer.print("(yymsp - {d})[1].minor.@\"{s}\" = ", .{ rp.rhs.len, rp.lhs.dttag });
        try writer.print("{s};", .{zLhs});
    }
    // Suffix code generation complete
    rp.codeSuffix = try Strsafe(string_builder.writer.buffer[0..string_builder.writer.end]);
    if (rp.codePrefix.len > 0 or rp.codeSuffix.len > 0) rp.noCode = false;
    return rc;
}

//
// Generate code which executes when the rule "rp" is reduced.  Write
// the code to "out".  Make sure lineno stays up-to-date.
//
fn emit_code(out: anytype, rp: *Rule, zyt: *Zitron, lineno: *usize) !void {
    if (zyt.opt.linenos) return emit_code_no_indent(out, rp, zyt, lineno);
    //
    // Generate code to do the reduce action
    try out.writeAll("        => {\n");
    lineno.* += 1;
    // Setup code prior to the #line directive
    if (rp.codePrefix.len > 0) {
        const extra: usize = if (try writeToIndent(out, rp.codePrefix, 12)) 1 else 0;
        lineno.* += mem.count(u8, rp.codePrefix, "\n") + extra;
    }
    if (rp.code.len > 0) {
        const extra: usize = if (try writeToIndent(out, rp.code, 12)) 1 else 0;
        lineno.* += mem.count(u8, rp.code, "\n") + extra;
    }
    // Generate breakdown code that occurs after the #line directive
    if (rp.codeSuffix.len > 0) {
        const more_extra: usize = if (try writeToIndent(out, rp.codeSuffix, 12)) 1 else 0;
        lineno.* += mem.count(u8, rp.codeSuffix, "\n") + more_extra;
    }
    try out.writeAll("        },\n");
    lineno.* += 1;

    return;
}

fn emit_code_no_indent(out: anytype, rp: *Rule, zyt: *Zitron, lineno: *usize) !void {
    // Generate code to do the reduce action
    try out.writeAll("        => {\n");
    lineno.* += 1;
    // Setup code prior to the #line directive
    if (rp.codePrefix.len > 0) {
        try out.print("{s}", .{rp.codePrefix});
        lineno.* += mem.count(u8, rp.codePrefix, "\n");
    }
    // Generate code to do the reduce action
    if (rp.code.len > 0) {
        if (zyt.opt.linenos) {
            lineno.* += 1;
            try tplt_linedir(out, rp.line, zyt.filename);
        }
        try out.print("{s}", .{rp.code});
        lineno.* += mem.count(u8, rp.code, "\n");
        if (rp.code[rp.code.len - 1] != '\n') {
            try out.writeByte('\n');
            lineno.* += 1;
        }
        if (zyt.opt.linenos) {
            lineno.* += 1;
            try tplt_linedir(out, lineno.*, zyt.outname);
        }
    }

    // Generate breakdown code that occurs after the #line directive
    if (rp.codeSuffix.len > 0) {
        try out.print("{s}", .{rp.codeSuffix});
        lineno.* += mem.count(u8, rp.codeSuffix, "\n");
        if (rp.codeSuffix[rp.codeSuffix.len - 1] != '\n') {
            try out.writeByte('\n');
            lineno.* += 1;
        }
    }
    try out.writeAll("},\n");
    lineno.* += 1;
    return;
}

/// Check to make sure we can print the filename (no tabs no spaces, is Unicode)
fn check_filename(filename: []const u8) !void {
    if (std.mem.indexOfScalar(u8, filename, '\n')) |_| return error.FileNameHasNewline;
    if (std.mem.indexOfScalar(u8, filename, '\t')) |_| return error.FileNameHasTab;
    if (!std.unicode.utf8ValidateSlice(filename)) return error.FileNameNotUtf8;
}

/// Print the Token enum
fn print_token_enum(zyt: *Zitron, out: anytype, plineno: *usize) !void {
    const tok_enum = zyt.defines.get("🍋TOKEN_ENUM").?;
    if (zyt.token_enum_integer.len > 0) {
        try out.print(
            "pub const {s} = enum({s}) {{\n",
            .{ tok_enum, zyt.token_enum_integer },
        );
    } else {
        try out.print(
            "pub const {s} = enum(u{d}) {{\n",
            .{ tok_enum, std.math.log2_int_ceil(usize, zyt.nterminal + 1) },
        );
    }
    plineno.* += 1;
    try out.writeAll("    end_of_input = 0,\n");
    for (zyt.symbols[1..zyt.nterminal]) |t_sym| {
        try out.print("    {s},\n", .{t_sym.name});
        plineno.* += 1;
    }
    try out.writeAll("};\n");
    plineno.* += 1;
}

/// Print the definition of the union used for the parser's data stack.
/// This union contains fields for every possible data type for tokens
/// and nonterminals.  In the process of computing and printing this
/// union, also set the ".dtnum" field of every terminal and nonterminal
/// symbol.
fn print_stack_union(
    /// The output stream
    out: anytype,
    /// The main info structure for this parser
    zyt: *Zitron,
    /// Pointer to the line number
    plineno: *usize,
) !void {
    //| NOTE: This creates an ad-hoc hash table, because C.  Alas, I
    //| cannot in this case substitute a Zig data type, because the
    //| hash algorithm is load-bearing: it assigns a dtnum to Symbols
    //| and those end up in the output.  So it goes.

    //| Premise: we can borrow all the strings as []const u8, and just
    //| free the array of pointers.  Let's find out.

    //  Allocate and initialize types[] and allocate stddt[]
    const arraysize = zyt.nsymbol * 2; // Room for hash collisions
    const types = try zyt.allocator.alloc([]const u8, arraysize);
    defer zyt.allocator.free(types);
    @memset(types, "");
    // Build a hash table of datatypes. The ".dtnum" field of each symbol
    // is filled in with the hash index plus 1.  A ".dtnum" value of 0 is
    // used for terminal symbols.  If there is no %default_type defined then
    // 0 is also used as the .dtnum value for nonterminals which do not specify
    // a datatype using the %type directive.
    hash: for (zyt.symbols[0..zyt.nsymbol]) |sp| {
        if (sp == zyt.errsym) {
            sp.dtnum = arraysize + 1;
            continue :hash;
        }
        if (sp.type != .nonterminal or (sp.datatype.len == 0 and zyt.vartype.len == 0)) {
            dbgassert(sp.dtnum == 0);
            continue :hash;
        }
        const d_raw = if (sp.datatype.len > 0) sp.datatype else zyt.vartype;
        const stddt = mem.trim(u8, d_raw, C_SPACE);
        if (zyt.tokentype.len > 0 and std.mem.eql(u8, zyt.tokentype, stddt)) {
            dbgassert(sp.dtnum == 0);
            continue :hash;
        }
        var hash: u32 = 0;
        for (stddt) |b| {
            hash = hash *% 53 +% b;
        }
        hash = (hash & 0x7fff_ffff) % arraysize;
        probe: while (types[hash].len > 0) {
            if (mem.eql(u8, types[hash], stddt)) {
                sp.dtnum = hash + 1;
                break :probe;
            }
            hash += 1;
            if (hash >= arraysize) hash = 0;
        }
        if (types[hash].len == 0) {
            sp.dtnum = hash + 1;
            types[hash] = stddt; // borrowed for the duration
        }
    }
    var lineno = plineno.*;
    // Decorate all symbols with the appropriate .dttag
    const t_name = if (zyt.tokentype.len > 0) mem.trim(u8, zyt.tokentype, C_SPACE) else "void";
    for (zyt.symbols[0..zyt.nsymbol]) |sp| {
        if (sp == zyt.errsym) {
            sp.dttag = sp.name;
        } else if (sp.dtnum == 0) {
            sp.dttag = t_name;
        } else {
            sp.dttag = types[sp.dtnum - 1];
        }
    }
    // zig fmt: off
    try out.print("const YY_TOKEN_TYPE = {s};\n", .{ t_name }); lineno += 1;
    try out.writeAll("pub const YYMINORTYPE = minor: {\n"); lineno += 1;
    try out.writeAll("    @setRuntimeSafety(false);\n"); lineno += 1;
    try out.writeAll("    break :minor union {\n"); lineno += 1;
    try out.print("        @\"{s}\": YY_TOKEN_TYPE,\n", .{t_name}); lineno += 1;
    t_print: for (types, 0..) |variant, i| {
        _ = i;
        if (variant.len == 0) continue :t_print;
        // try out.print("      // yy{d}: {s},\n", .{ i + 1, variant }); lineno += 1;
        try out.print("        @\"{s}\": {s}, \n", .{variant, variant}); lineno += 1;
    }
    if (zyt.errsym) |errsym| if (errsym.useCnt > 0) {
        try out.print("        @\"{s}\": usize,\n", .{errsym.dttag}); lineno += 1;
    };
    try out.writeAll("    };\n};\n");
    // zig fmt: on
    lineno += 2;
    plineno.* = lineno;
}

// Return the name of a Zig datatype able to represent values between
// lwr and upr, inclusive.  If pnByte != null then also write the sizeof
// for that type (1, 2, or 4) into *pnByte.  If "loose" we always make
// sure there's room for one more (else branches on switches)
fn minimum_size_type(lwr: i64, upr: u32, pNbyte: ?*u8, loose: bool) []const u8 {
    var zType: []const u8 = "";
    var nByte: ?u8 = null;
    const minus: usize = if (loose) 2 else 1;
    // TODO: It would be more elegant to use the minimum power-of-two
    // to represent these.
    if (lwr >= 0) {
        if (upr <= (1 << 8) - minus) {
            zType = "u8";
            nByte = 1;
        } else if (upr <= (1 << 16) - minus) {
            zType = "u16";
            nByte = 2;
        } else {
            zType = "u32";
            nByte = 4; // redundant
        }
    } else {
        if (lwr >= -127 and upr <= 128 - minus) {
            zType = "i8";
            nByte = 1;
        } else if (lwr >= -32767 and upr < 32768 - minus) {
            zType = "i16";
            nByte = 2;
        } else {
            zType = "i32";
            nByte = 4;
        }
    }
    if (pNbyte) |pNb| pNb.* = nByte.?;
    return zType;
}

/// Each state contains a set of token transactions and a set of
/// nonterminal transactions.  Each of these sets makes an instance
/// of the following structure.  An array of these structures is used
/// to order the creation of entries in the yy_action[] table.
pub const AxSet = struct {
    /// A pointer to a state
    stp: *State,
    /// True to use tokens.  False for non-terminals
    isTkn: bool,
    /// Number of actions
    nAction: u32,
    /// Original order of action sets
    iOrder: u32,

    pub const empty: AxSet = .{
        .stp = undefined,
        .isTkn = false,
        .nAction = 0,
        .iOrder = 0,
    };
};

/// Compare to axset structures for sorting purposes
fn axset_compare(_: void, p1: AxSet, p2: AxSet) bool {
    if (p1.nAction > p2.nAction) return true;
    if (p1.nAction < p2.nAction) return false;
    return p1.iOrder < p2.iOrder;
}

// /*
// ** Write text on "out" that describes the rule "rp".
// */
fn writeRuleText(out: anytype, rp: *Rule) !void {
    try out.print("{s} ::=", .{rp.lhs.name});
    for (rp.rhs) |sp| {
        if (sp.type != .multiterminal) {
            try out.print(" {s}", .{sp.name});
        } else {
            try out.print(" {s}", .{sp.subsym[0].name});
            for (sp.subsym[1..]) |ssp| {
                try out.print("|{s}", .{ssp.name});
            }
        }
    }
}

fn writeSqlStringContent(out: anytype, str: []const u8) !void {
    for (str) |ch| {
        try out.writeByte(ch);
        if (ch == '\'') try out.writeByte('\'');
    }
}

fn writeSqlString(out: anytype, str: []const u8) !void {
    try out.writeByte('\'');
    try writeSqlStringContent(out, str);
    try out.writeByte('\'');
}

fn writeSqlNullableString(out: anytype, str: []const u8) !void {
    if (str.len == 0) {
        try out.writeAll("NULL");
    } else {
        try writeSqlString(out, str);
    }
}

fn writeSqlBool(out: anytype, value: bool) !void {
    try out.writeAll(if (value) "TRUE" else "FALSE");
}

fn writeRuleTextSqlString(out: anytype, rp: *Rule) !void {
    try out.writeByte('\'');
    try writeSqlStringContent(out, rp.lhs.name);
    try out.writeAll(" ::=");
    for (rp.rhs) |sp| {
        try out.writeByte(' ');
        if (sp.type != .multiterminal) {
            try writeSqlStringContent(out, sp.name);
        } else {
            try writeSqlStringContent(out, sp.subsym[0].name);
            for (sp.subsym[1..]) |ssp| {
                try out.writeByte('|');
                try writeSqlStringContent(out, ssp.name);
            }
        }
    }
    try out.writeByte('\'');
}

fn writeImplSignatureWith(out: anytype, impl: *const Impl, comptime sql_escape: bool) !void {
    const write = struct {
        fn text(writer: anytype, bytes: []const u8) !void {
            if (sql_escape) {
                try writeSqlStringContent(writer, bytes);
            } else {
                try writer.writeAll(bytes);
            }
        }
    }.text;

    try write(out, impl.name);
    try out.writeByte('(');
    if (impl.lhsalias.len > 0) try write(out, impl.lhsalias);
    if (rhsAliasesHaveNames(impl.rhsalias)) {
        try out.writeAll("; ");
        for (impl.rhsalias, 0..) |alias, i| {
            if (i > 0) try out.writeAll(", ");
            try write(out, alias);
        }
    }
    try out.writeByte(')');
}

fn writeImplSignature(out: anytype, impl: *const Impl) !void {
    try writeImplSignatureWith(out, impl, false);
}

fn writeSqlImplSignature(out: anytype, impl: *const Impl) !void {
    try out.writeByte('\'');
    try writeImplSignatureWith(out, impl, true);
    try out.writeByte('\'');
}

fn findImplForRule(rp: *Rule) ?*Impl {
    for (impl_safe.impls.values()) |impl| {
        if (impl.rule == rp) return impl;
    }
    return null;
}

fn configIsBasis(stp: *State, cfp: *Config) bool {
    var maybe_bp = stp.bp;
    while (maybe_bp) |bp| : (maybe_bp = bp.bp) {
        if (bp == cfp) return true;
    }
    return false;
}

fn actionTargetState(ap: *Action) ?u32 {
    return switch (ap.type) {
        .shift, .ssconflict, .sh_resolved => ap.x.stp.statenum,
        else => null,
    };
}

fn actionTargetRule(ap: *Action) ?u32 {
    return switch (ap.type) {
        .reduce, .shiftreduce, .srconflict, .rrconflict, .rd_resolved => ap.x.rp.?.iRule,
        else => null,
    };
}

fn stateDefaultAction(zyt: *Zitron, stp: *State) u32 {
    if (stp.iDfltReduce < 0) return zyt.errAction;
    return uint(stp.iDfltReduce) + zyt.minReduce;
}

fn writeJsonInt(out: anytype, first: *bool, value: anytype) !void {
    if (!first.*) try out.writeByte(',');
    first.* = false;
    try out.print("{d}", .{value});
}

fn beginParserTable(sql: anytype, name: []const u8, len: usize) !bool {
    try sql.writeAll("INSERT INTO parser_table(name,len,json)VALUES(");
    try writeSqlString(sql, name);
    try sql.print(",{d},'[", .{len});
    return true;
}

fn endParserTable(sql: anytype) !void {
    try sql.writeAll("]');\n");
}

fn emitParserConstants(zyt: *Zitron, pActtab: *const ActTable, sql: anytype) !void {
    try sql.writeAll("CREATE TABLE parser_constant(\n" ++
        "  name TEXT PRIMARY KEY,\n" ++
        "  value INTEGER NOT NULL\n" ++
        ");\n");

    const constants = .{
        .{ "YYNSTATE", zyt.nxstate },
        .{ "YYNRULE", zyt.nrule },
        .{ "YYNRULE_WITH_ACTION", zyt.nruleWithAction },
        .{ "YYNTOKEN", zyt.nterminal },
        .{ "YY_MAX_SHIFT", zyt.nxstate - 1 },
        .{ "YY_MIN_SHIFTREDUCE", zyt.minShiftReduce },
        .{ "YY_MAX_SHIFTREDUCE", zyt.minShiftReduce + zyt.nrule - 1 },
        .{ "YY_ERROR_ACTION", zyt.errAction },
        .{ "YY_ACCEPT_ACTION", zyt.accAction },
        .{ "YY_NO_ACTION", zyt.noAction },
        .{ "YY_MIN_REDUCE", zyt.minReduce },
        .{ "YY_MAX_REDUCE", zyt.minReduce + zyt.nrule - 1 },
        .{ "YY_ACTTAB_COUNT", pActtab.actionSize() },
        .{ "YY_SHIFT_MIN", pActtab.mnTknOfst },
        .{ "YY_SHIFT_MAX", pActtab.mxTknOfst },
        .{ "YY_REDUCE_MIN", pActtab.mnNtOfst },
        .{ "YY_REDUCE_MAX", pActtab.mxNtOfst },
    };

    inline for (constants) |constant| {
        try sql.writeAll("INSERT INTO parser_constant(name,value)VALUES(");
        try writeSqlString(sql, constant[0]);
        try sql.print(",{d});\n", .{constant[1]});
    }

    {
        var n = zyt.nxstate;
        while (n > 0 and zyt.sorted[n - 1].iTknOfst == NO_OFFSET) : (n -= 1) {}
        try sql.print("INSERT INTO parser_constant(name,value)VALUES('YY_SHIFT_COUNT',{d});\n", .{n - 1});
    }
    {
        var n = zyt.nxstate;
        while (n > 0 and zyt.sorted[n - 1].iNtOfst == NO_OFFSET) : (n -= 1) {}
        try sql.print("INSERT INTO parser_constant(name,value)VALUES('YY_REDUCE_COUNT',{d});\n", .{n - 1});
    }
}

fn emitParserTables(zyt: *Zitron, pActtab: *const ActTable, sql: anytype) !void {
    try sql.writeAll("CREATE TABLE parser_table(\n" ++
        "  name TEXT PRIMARY KEY,\n" ++
        "  len INTEGER NOT NULL,\n" ++
        "  json TEXT NOT NULL\n" ++
        ");\n");

    {
        const n = pActtab.actionSize();
        var first = try beginParserTable(sql, "yy_action", n);
        for (0..n) |i| {
            var action = pActtab.yyaction(i);
            if (action < 0) action = @intCast(zyt.noAction);
            try writeJsonInt(sql, &first, action);
        }
        try endParserTable(sql);
    }
    {
        const n = pActtab.lookaheadSize();
        const nLookAhead = zyt.nterminal + pActtab.actionSize();
        var first = try beginParserTable(sql, "yy_lookahead", nLookAhead);
        var i: usize = 0;
        while (i < n) : (i += 1) {
            var lookahead = pActtab.yylookahead(i);
            if (lookahead < 0) lookahead = @intCast(zyt.nsymbol);
            try writeJsonInt(sql, &first, lookahead);
        }
        while (i < nLookAhead) : (i += 1) {
            try writeJsonInt(sql, &first, zyt.nterminal);
        }
        try endParserTable(sql);
    }
    {
        var n = zyt.nxstate;
        while (n > 0 and zyt.sorted[n - 1].iTknOfst == NO_OFFSET) : (n -= 1) {}
        var first = try beginParserTable(sql, "yy_shift_ofst", n);
        for (0..n) |i| {
            var ofst = zyt.sorted[i].iTknOfst;
            if (ofst == NO_OFFSET) ofst = @intCast(pActtab.actionSize());
            try writeJsonInt(sql, &first, ofst);
        }
        try endParserTable(sql);
    }
    {
        var n = zyt.nxstate;
        while (n > 0 and zyt.sorted[n - 1].iNtOfst == NO_OFFSET) : (n -= 1) {}
        var first = try beginParserTable(sql, "yy_reduce_ofst", n);
        for (0..n) |i| {
            var ofst = zyt.sorted[i].iNtOfst;
            if (ofst == NO_OFFSET) ofst = pActtab.mnNtOfst - 1;
            try writeJsonInt(sql, &first, ofst);
        }
        try endParserTable(sql);
    }
    {
        var first = try beginParserTable(sql, "yy_default", zyt.nxstate);
        for (0..zyt.nxstate) |i| {
            try writeJsonInt(sql, &first, stateDefaultAction(zyt, zyt.sorted[i]));
        }
        try endParserTable(sql);
    }
    if (zyt.has_fallback) {
        var first = try beginParserTable(sql, "yyFallback", zyt.nterminal);
        for (0..zyt.nterminal) |i| {
            const sp = zyt.symbols[i];
            try writeJsonInt(sql, &first, if (sp.fallback) |fallback| fallback.index else 0);
        }
        try endParserTable(sql);
    }
    {
        var first = try beginParserTable(sql, "yyRuleInfoLhs", zyt.nrule);
        var m_rp: ?*Rule = zyt.rule;
        while (m_rp) |rp| : (m_rp = rp.next) {
            try writeJsonInt(sql, &first, rp.lhs.index);
        }
        try endParserTable(sql);
    }
    {
        var first = try beginParserTable(sql, "yyRuleInfoNRhs", zyt.nrule);
        var m_rp: ?*Rule = zyt.rule;
        while (m_rp) |rp| : (m_rp = rp.next) {
            const nrhs: int = if (rp.rhs.len == 0) 0 else -cast(int, rp.rhs.len);
            try writeJsonInt(sql, &first, nrhs);
        }
        try endParserTable(sql);
    }
}

fn ReportSql(zyt: *Zitron, pActtab: *const ActTable, sql: anytype) !void {
    try sql.writeAll("BEGIN;\n" ++
        "CREATE TABLE symbol(\n" ++
        "  id INTEGER PRIMARY KEY,\n" ++
        "  name TEXT NOT NULL,\n" ++
        "  isTerminal BOOLEAN NOT NULL,\n" ++
        "  fallback INTEGER REFERENCES symbol DEFERRABLE INITIALLY DEFERRED,\n" ++
        "  type TEXT NOT NULL,\n" ++
        "  precedence INTEGER,\n" ++
        "  associativity TEXT,\n" ++
        "  lambda BOOLEAN NOT NULL,\n" ++
        "  hasContent BOOLEAN NOT NULL\n" ++
        ");\n");
    for (0..zyt.nsymbol) |i| {
        const sp = zyt.symbols[i];
        try sql.print("INSERT INTO symbol(id,name,isTerminal,fallback,type,precedence,associativity,lambda,hasContent)VALUES({d},", .{i});
        try writeSqlString(sql, sp.name);
        try sql.writeByte(',');
        try writeSqlBool(sql, i < zyt.nterminal);
        try sql.writeByte(',');
        if (sp.fallback) |fp| {
            try sql.print("{d}", .{fp.index});
        } else {
            try sql.writeAll("NULL");
        }
        try sql.writeByte(',');
        try writeSqlString(sql, if (i < zyt.nterminal) "terminal" else @tagName(sp.type));
        try sql.writeByte(',');
        if (sp.prec) |prec| {
            try sql.print("{d}", .{prec});
        } else {
            try sql.writeAll("NULL");
        }
        try sql.writeByte(',');
        if (sp.prec != null and sp.assoc != .unk) {
            try writeSqlString(sql, @tagName(sp.assoc));
        } else {
            try sql.writeAll("NULL");
        }
        try sql.writeByte(',');
        try writeSqlBool(sql, sp.lambda);
        try sql.writeByte(',');
        try writeSqlBool(sql, sp.bContent);
        try sql.writeAll(");\n");
    }
    try sql.writeAll("CREATE TABLE symbol_firstset(\n" ++
        "  nonterminal INTEGER REFERENCES symbol(id),\n" ++
        "  terminal INTEGER REFERENCES symbol(id),\n" ++
        "  PRIMARY KEY(nonterminal, terminal)\n" ++
        ");\n");
    for (zyt.nterminal..zyt.nsymbol) |i| {
        const sp = zyt.symbols[i];
        for (0..zyt.nterminal) |j| {
            if (sp.firstset.len > 0 and sp.firstset[j]) {
                try sql.print("INSERT INTO symbol_firstset(nonterminal,terminal)VALUES({d},{d});\n", .{ i, j });
            }
        }
    }

    try sql.writeAll("CREATE TABLE rule(\n" ++
        "  ruleid INTEGER PRIMARY KEY,\n" ++
        "  lhs INTEGER REFERENCES symbol(id),\n" ++
        "  txt TEXT,\n" ++
        "  nrhs INTEGER NOT NULL,\n" ++
        "  lhsAlias TEXT,\n" ++
        "  ruleLine INTEGER NOT NULL,\n" ++
        "  codeLine INTEGER NOT NULL,\n" ++
        "  precedenceSymbol INTEGER REFERENCES symbol(id),\n" ++
        "  lhsStart BOOLEAN NOT NULL,\n" ++
        "  noCode BOOLEAN NOT NULL,\n" ++
        "  canReduce BOOLEAN NOT NULL,\n" ++
        "  doesReduce BOOLEAN NOT NULL,\n" ++
        "  neverReduce BOOLEAN NOT NULL,\n" ++
        "  originalIndex INTEGER NOT NULL,\n" ++
        "  implName TEXT,\n" ++
        "  implSignature TEXT\n" ++
        ");\n" ++
        "CREATE TABLE rulerhs(\n" ++
        "  ruleid INTEGER REFERENCES rule(ruleid),\n" ++
        "  pos INTEGER,\n" ++
        "  sym INTEGER REFERENCES symbol(id),\n" ++
        "  alt INTEGER NOT NULL DEFAULT 0,\n" ++
        "  alias TEXT\n" ++
        ");\n" ++
        "CREATE TABLE rule_impl(\n" ++
        "  ruleid INTEGER PRIMARY KEY REFERENCES rule(ruleid),\n" ++
        "  name TEXT NOT NULL,\n" ++
        "  signature TEXT NOT NULL,\n" ++
        "  line INTEGER NOT NULL,\n" ++
        "  lhsAlias TEXT\n" ++
        ");\n" ++
        "CREATE TABLE rule_impl_rhs(\n" ++
        "  ruleid INTEGER REFERENCES rule(ruleid),\n" ++
        "  pos INTEGER,\n" ++
        "  alias TEXT,\n" ++
        "  PRIMARY KEY(ruleid, pos)\n" ++
        ");\n");
    var i: usize = 0;
    var m_rp: ?*Rule = zyt.rule;
    // zig fmt: off
    while (m_rp) |rp| : ({i += 1; m_rp = rp.next;}) {
        // zig fmt: on
        dbgassert(i == rp.iRule);
        const maybe_impl = findImplForRule(rp);
        try sql.print("INSERT INTO rule(ruleid,lhs,txt,nrhs,lhsAlias,ruleLine,codeLine,precedenceSymbol,lhsStart,noCode,canReduce,doesReduce,neverReduce,originalIndex,implName,implSignature)VALUES({d},{d},", .{ rp.iRule, rp.lhs.index });
        try writeRuleTextSqlString(sql, rp);
        try sql.print(",{d},", .{rp.rhs.len});
        try writeSqlNullableString(sql, rp.lhsalias);
        try sql.print(",{d},{d},", .{ rp.ruleline, rp.line });
        if (rp.precsym) |precsym| {
            try sql.print("{d}", .{precsym.index});
        } else {
            try sql.writeAll("NULL");
        }
        try sql.writeByte(',');
        try writeSqlBool(sql, rp.lhsStart);
        try sql.writeByte(',');
        try writeSqlBool(sql, rp.noCode);
        try sql.writeByte(',');
        try writeSqlBool(sql, rp.canReduce);
        try sql.writeByte(',');
        try writeSqlBool(sql, rp.doesReduce);
        try sql.writeByte(',');
        try writeSqlBool(sql, rp.neverReduce);
        try sql.print(",{d},", .{rp.index});
        if (maybe_impl) |impl| {
            try writeSqlString(sql, impl.name);
            try sql.writeByte(',');
            try writeSqlImplSignature(sql, impl);
        } else {
            try sql.writeAll("NULL,NULL");
        }
        try sql.writeAll(");\n");
        if (maybe_impl) |impl| {
            try sql.print("INSERT INTO rule_impl(ruleid,name,signature,line,lhsAlias)VALUES({d},", .{rp.iRule});
            try writeSqlString(sql, impl.name);
            try sql.writeByte(',');
            try writeSqlImplSignature(sql, impl);
            try sql.print(",{d},", .{impl.line});
            try writeSqlNullableString(sql, impl.lhsalias);
            try sql.writeAll(");\n");
            for (impl.rhsalias, 0..) |alias, j| {
                try sql.print("INSERT INTO rule_impl_rhs(ruleid,pos,alias)VALUES({d},{d},", .{ rp.iRule, j });
                try writeSqlNullableString(sql, alias);
                try sql.writeAll(");\n");
            }
        }
        for (rp.rhs, 0..) |sp, j| {
            if (sp.type != .multiterminal) {
                try sql.print("INSERT INTO rulerhs(ruleid,pos,sym,alt,alias)VALUES({d},{d},{d},0,", .{ i, j, sp.index });
                try writeSqlNullableString(sql, rp.rhsalias[j]);
                try sql.writeAll(");\n");
            } else {
                for (sp.subsym, 0..) |ssp, alt| {
                    try sql.print("INSERT INTO rulerhs(ruleid,pos,sym,alt,alias)VALUES({d},{d},{d},{d},", .{ i, j, ssp.index, alt });
                    try writeSqlNullableString(sql, rp.rhsalias[j]);
                    try sql.writeAll(");\n");
                }
            }
        }
    }

    try sql.writeAll("CREATE TABLE state(\n" ++
        "  id INTEGER PRIMARY KEY,\n" ++
        "  is_emitted BOOLEAN NOT NULL,\n" ++
        "  n_token_actions INTEGER NOT NULL,\n" ++
        "  n_nonterminal_actions INTEGER NOT NULL,\n" ++
        "  token_offset INTEGER NOT NULL,\n" ++
        "  nonterminal_offset INTEGER NOT NULL,\n" ++
        "  default_reduce_rule INTEGER REFERENCES rule(ruleid),\n" ++
        "  default_action INTEGER NOT NULL,\n" ++
        "  autoreduce BOOLEAN NOT NULL\n" ++
        ");\n");
    for (zyt.sorted, 0..) |stp, order| {
        try sql.print("INSERT INTO state(id,is_emitted,n_token_actions,n_nonterminal_actions,token_offset,nonterminal_offset,default_reduce_rule,default_action,autoreduce)VALUES({d},", .{stp.statenum});
        try writeSqlBool(sql, order < zyt.nxstate);
        try sql.print(",{d},{d},{d},{d},", .{ stp.nTknAct, stp.nNtAct, stp.iTknOfst, stp.iNtOfst });
        if (stp.pDefltReduce) |rp| {
            try sql.print("{d}", .{rp.iRule});
        } else {
            try sql.writeAll("NULL");
        }
        try sql.print(",{d},", .{stateDefaultAction(zyt, stp)});
        try writeSqlBool(sql, stp.autoreduce);
        try sql.writeAll(");\n");
    }

    try sql.writeAll("CREATE TABLE configuration(\n" ++
        "  state_id INTEGER REFERENCES state(id),\n" ++
        "  ordinal INTEGER,\n" ++
        "  ruleid INTEGER REFERENCES rule(ruleid),\n" ++
        "  dot INTEGER NOT NULL,\n" ++
        "  is_basis BOOLEAN NOT NULL,\n" ++
        "  PRIMARY KEY(state_id, ordinal)\n" ++
        ");\n" ++
        "CREATE TABLE configuration_follow(\n" ++
        "  state_id INTEGER,\n" ++
        "  config_ordinal INTEGER,\n" ++
        "  terminal INTEGER REFERENCES symbol(id),\n" ++
        "  PRIMARY KEY(state_id, config_ordinal, terminal),\n" ++
        "  FOREIGN KEY(state_id, config_ordinal) REFERENCES configuration(state_id, ordinal)\n" ++
        ");\n");
    for (zyt.sorted) |stp| {
        var ordinal: usize = 0;
        var m_cfp: ?*Config = stp.cfp;
        while (m_cfp) |cfp| : ({
            ordinal += 1;
            m_cfp = cfp.next;
        }) {
            try sql.print("INSERT INTO configuration(state_id,ordinal,ruleid,dot,is_basis)VALUES({d},{d},{d},{d},", .{ stp.statenum, ordinal, cfp.rp.iRule, cfp.dot });
            try writeSqlBool(sql, configIsBasis(stp, cfp));
            try sql.writeAll(");\n");
            for (0..zyt.nterminal) |j| {
                if (cfp.fws.len > 0 and cfp.fws[j]) {
                    try sql.print("INSERT INTO configuration_follow(state_id,config_ordinal,terminal)VALUES({d},{d},{d});\n", .{ stp.statenum, ordinal, j });
                }
            }
        }
    }

    try sql.writeAll("CREATE TABLE action_kind(\n" ++
        "  kind TEXT PRIMARY KEY\n" ++
        ");\n");
    inline for (std.meta.tags(E_Action)) |kind| {
        if (kind != ._not_initialized) {
            try sql.writeAll("INSERT INTO action_kind(kind)VALUES(");
            try writeSqlString(sql, @tagName(kind));
            try sql.writeAll(");\n");
        }
    }

    try sql.writeAll("CREATE TABLE action(\n" ++
        "  state_id INTEGER REFERENCES state(id),\n" ++
        "  ordinal INTEGER,\n" ++
        "  lookahead INTEGER REFERENCES symbol(id),\n" ++
        "  lookahead_name TEXT NOT NULL,\n" ++
        "  kind TEXT NOT NULL REFERENCES action_kind(kind),\n" ++
        "  target_state INTEGER REFERENCES state(id),\n" ++
        "  target_rule INTEGER REFERENCES rule(ruleid),\n" ++
        "  computed_action INTEGER,\n" ++
        "  is_conflict BOOLEAN NOT NULL,\n" ++
        "  is_resolved BOOLEAN NOT NULL,\n" ++
        "  optimized_from_symbol INTEGER REFERENCES symbol(id),\n" ++
        "  PRIMARY KEY(state_id, ordinal)\n" ++
        ");\n");
    for (zyt.sorted) |stp| {
        var ordinal: usize = 0;
        var m_ap = stp.ap;
        while (m_ap) |ap| : ({
            ordinal += 1;
            m_ap = ap.next;
        }) {
            try sql.print("INSERT INTO action(state_id,ordinal,lookahead,lookahead_name,kind,target_state,target_rule,computed_action,is_conflict,is_resolved,optimized_from_symbol)VALUES({d},{d},", .{ stp.statenum, ordinal });
            if (ap.sp.index < zyt.nsymbol) {
                try sql.print("{d}", .{ap.sp.index});
            } else {
                try sql.writeAll("NULL");
            }
            try sql.writeByte(',');
            try writeSqlString(sql, ap.sp.name);
            try sql.writeByte(',');
            try writeSqlString(sql, @tagName(ap.type));
            try sql.writeByte(',');
            if (actionTargetState(ap)) |target_state| {
                try sql.print("{d}", .{target_state});
            } else {
                try sql.writeAll("NULL");
            }
            try sql.writeByte(',');
            if (actionTargetRule(ap)) |target_rule| {
                try sql.print("{d}", .{target_rule});
            } else {
                try sql.writeAll("NULL");
            }
            try sql.writeByte(',');
            if (compute_action(zyt, ap)) |computed| {
                try sql.print("{d}", .{computed});
            } else {
                try sql.writeAll("NULL");
            }
            try sql.writeByte(',');
            try writeSqlBool(sql, ap.type == .ssconflict or ap.type == .srconflict or ap.type == .rrconflict);
            try sql.writeByte(',');
            try writeSqlBool(sql, ap.type == .sh_resolved or ap.type == .rd_resolved);
            try sql.writeByte(',');
            if (ap.spOpt) |spOpt| {
                try sql.print("{d}", .{spOpt.index});
            } else {
                try sql.writeAll("NULL");
            }
            try sql.writeAll(");\n");
        }
    }

    try emitParserConstants(zyt, pActtab, sql);
    try emitParserTables(zyt, pActtab, sql);
    try sql.writeAll("COMMIT;\n");
}

/// Perform 'macroexpansion' of the emoji-marked identifiers in the template.
fn macroReplace(zyt: *Zitron, in: [:0]const u8) ![:0]const u8 {
    var mark: usize = 0;
    var in_writer = try AllocatingWriter.initCapacity(zyt.allocator, in.len);
    defer in_writer.deinit();
    var in_write = &in_writer.writer;
    while (std.mem.indexOfPos(u8, in, mark, "🍋")) |fruit| {
        try in_write.writeAll(in[mark..fruit]);
        var post_fruit = fruit + 4;
        while (('A' <= in[post_fruit] and in[post_fruit] <= 'Z') or
            ('a' <= in[post_fruit] and in[post_fruit] <= 'z') or
            in[post_fruit] == '_') : (post_fruit += 1)
        {}
        const macro = in[fruit..post_fruit];
        // std.debug.print("Fruit: '{s}'\n", .{macro});
        const mac_replace = zyt.defines.get(macro);
        if (mac_replace) |replacement| {
            // std.debug.print("Replaced: '{s}'\n", .{replacement});
            try in_write.writeAll(replacement);
        } else {
            // std.debug.print("Nothing!\n", .{});
        }
        mark = post_fruit;
    }
    try in_write.writeAll(in[mark..in.len]);
    const in_out = try in_writer.toOwnedSliceSentinel(0);
    return in_out;
}

//| [4287]

/// Generate C code for the parser
fn ReportTable(
    zyt: *Zitron,
) !void {
    zyt.minShiftReduce = zyt.nstate;
    zyt.errAction = zyt.minShiftReduce + zyt.nrule;
    zyt.accAction = zyt.errAction + 1;
    zyt.noAction = zyt.accAction + 1;
    zyt.minReduce = zyt.noAction + 1;
    zyt.maxAction = zyt.minReduce + zyt.nrule;

    const free_buffer, const in = try tplt_open(zyt);
    defer if (free_buffer) zyt.allocator.free(in);
    try assign_outname(zyt, ".zig", true);
    if (zyt.opt.fifo) {
        var out_buffer: [4096]u8 = undefined;
        var stdout_writer = std.Io.File.stdout().writer(zyt.io, &out_buffer);
        const out = &stdout_writer.interface;
        try reportTableImpl(zyt, in, out);
        try out.flush();
        return;
    }
    const m_out_fh = try open_file(zyt, zyt.outname, .{});
    if (m_out_fh) |fh| {
        defer fh.close(zyt.io);
        var out_buffer: [4096]u8 = undefined;
        var f_writer = fh.writer(zyt.io, &out_buffer);
        const out = &f_writer.interface;
        try reportTableImpl(zyt, in, out);
        try out.flush();
    } else {} // No file handle
}

fn reportTableImpl(
    zyt: *Zitron,
    in_template: [:0]const u8,
    out: anytype,
) !void {
    var lineno: usize = 1;
    // Macros
    //
    // Zitron looks for 🍋 followed by a predictable identifier-like pattern,
    // then looks that string up in `zyt.defines`.  Results are used as
    // replacements, undefined values are simply removed.
    if (zyt.arg.len > 0) {
        const arg_trimmed = mem.trim(u8, zyt.arg, C_SPACE);
        const i = std.mem.indexOfScalar(u8, arg_trimmed, ':') orelse 0;
        if (i == 0) {
            std.debug.print(
                "Warning: %extra_argument should look like `arg: Type`, not `{s}`\n",
                .{zyt.arg},
            );
        }
        const arg = arg_trimmed[0..i];
        const allocator = zyt.allocator;
        {
            const arg_sdecl = try std.fmt.allocPrint(allocator, "{s},", .{arg_trimmed});
            errdefer allocator.free(arg_sdecl);
            try zyt.defines.put(allocator, "🍋ARG_SDECL", arg_sdecl);
        }
        {
            const arg_pdecl = try std.fmt.allocPrint(allocator, ", {s}", .{arg_trimmed});
            errdefer allocator.free(arg_pdecl);
            try zyt.defines.put(allocator, "🍋ARG_PDECL", arg_pdecl);
        }
        { // NOTE: ARG_PARAM is not used in lempar.c, so, Zitron isn't using it either.
            const arg_param = try std.fmt.allocPrint(allocator, "{s}", .{arg});
            errdefer allocator.free(arg_param);
            try zyt.defines.put(allocator, "🍋ARG_PARAM", arg_param);
        }
        {
            const arg_fetch = try std.fmt.allocPrint(
                allocator,
                "var {s} = yypParser.{s}; _ = .{{&{s}}};",
                .{ arg, arg, arg },
            );
            errdefer allocator.free(arg_fetch);
            try zyt.defines.put(allocator, "🍋ARG_FETCH", arg_fetch);
        }
        {
            const arg_store = try std.fmt.allocPrint(
                allocator,
                "yypParser.{s} = {s};",
                .{ arg, arg },
            );
            errdefer allocator.free(arg_store);
            try zyt.defines.put(allocator, "🍋ARG_STORE", arg_store);
        }
    }
    if (zyt.ctx.len > 0) {
        const ctx_trimmed = mem.trim(u8, zyt.ctx, C_SPACE);
        const i = std.mem.indexOfScalar(u8, ctx_trimmed, ':') orelse 0;
        if (i == 0) {
            std.debug.print(
                "Warning: %extra_context should look like `arg: Type`, not `{s}`\n",
                .{zyt.ctx},
            );
        }
        const ctx = ctx_trimmed[0..i];
        const allocator = zyt.allocator;
        {
            const ctx_sdecl = try std.fmt.allocPrint(allocator, "{s},", .{ctx_trimmed});
            errdefer allocator.free(ctx_sdecl);
            try zyt.defines.put(allocator, "🍋CTX_SDECL", ctx_sdecl);
        }
        {
            const ctx_pdecl = try std.fmt.allocPrint(allocator, ", {s}", .{ctx_trimmed});
            errdefer allocator.free(ctx_pdecl);
            try zyt.defines.put(allocator, "🍋CTX_PDECL", ctx_pdecl);
        }
        {
            const ctx_param = try std.fmt.allocPrint(allocator, "{s}", .{ctx});
            errdefer allocator.free(ctx_param);
            try zyt.defines.put(allocator, "🍋CTX_PARAM", ctx_param);
        }
        {
            const ctx_fetch = try std.fmt.allocPrint(
                allocator,
                "var {s} = yypParser.{s}; _ = .{{&{s}}};",
                .{ ctx, ctx, ctx },
            );
            errdefer allocator.free(ctx_fetch);
            try zyt.defines.put(allocator, "🍋CTX_FETCH", ctx_fetch);
        }
        {
            const ctx_store = try std.fmt.allocPrint(
                allocator,
                "yypParser.{s} = {s};",
                .{ ctx, ctx },
            );
            errdefer allocator.free(ctx_store);
            try zyt.defines.put(allocator, "🍋CTX_STORE", ctx_store);
        }

        {
            const ctx_guard = try std.fmt.allocPrint(allocator, "_ = .{{&{s}}};", .{ctx});
            errdefer allocator.free(ctx_guard);
            try zyt.defines.put(allocator, "🍋CTX_GUARD", ctx_guard);
        }
    }
    {
        const t_name = if (zyt.tokentype.len > 0) mem.trim(u8, zyt.tokentype, C_SPACE) else "void";
        const tok_field = try std.fmt.allocPrint(zyt.allocator, "@\"{s}\"", .{t_name});
        try zyt.defines.put(zyt.allocator, "🍋TOKEN_FIELD", tok_field);
    }
    if (zyt.token_enum.len > 0) {
        try zyt.defines.put(zyt.allocator, "🍋TOKEN_ENUM", try zyt.allocator.dupe(u8, zyt.token_enum));
    } else {
        try zyt.defines.put(zyt.allocator, "🍋TOKEN_ENUM", try zyt.allocator.dupe(u8, "TokenKind"));
    }
    if (zyt.name.len > 0) {
        try zyt.defines.put(zyt.allocator, "🍋PARSER_NAME", try zyt.allocator.dupe(u8, zyt.name));
    } else {
        try zyt.defines.put(zyt.allocator, "🍋PARSER_NAME", try zyt.allocator.dupe(u8, "Parser"));
    }
    if (zyt.error_type.len > 0) {
        try zyt.defines.put(zyt.allocator, "🍋PARSER_ERROR", try zyt.allocator.dupe(u8, zyt.error_type));
    }
    if (zyt.trace_writer.len > 0) {
        const trace = mem.trim(u8, zyt.trace_writer, C_SPACE);
        { // 🍋TRACE_ACCEPT
            const trace_accept = try std.fmt.allocPrint(
                zyt.allocator,
                \\{s}.print("{{s}}ACCEPT!\n",
                \\    .{{yyTracePrompt}}) catch {{}};
            ,
                .{trace},
            );
            errdefer zyt.allocator.free(trace_accept);
            try zyt.defines.put(zyt.allocator, "🍋TRACE_ACCEPT", trace_accept);
        }
        { // 🍋TRACE_DISCARD
            const trace_discard = try std.fmt.allocPrint(
                zyt.allocator,
                \\{s}.print("{{s}}Discard input token {{s}}\n",
                \\                            .{{ yyTracePrompt, yyTokenName[yymajor] }}) catch {{}};
            ,
                .{trace},
            );
            errdefer zyt.allocator.free(trace_discard);
            try zyt.defines.put(zyt.allocator, "🍋TRACE_DISCARD", trace_discard);
        }
        { // 🍋TRACE_FALLBACK
            const trace_fallback = try std.fmt.allocPrint(
                zyt.allocator,
                \\{s}.print("{{s}}FALLBACK {{s}} => {{s}}\n",
                \\                            .{{ yyTracePrompt, yyTokenName[yy_lookahead], yyTokenName[iFallback] }}) catch {{}};
            ,
                .{trace},
            );
            errdefer zyt.allocator.free(trace_fallback);
            try zyt.defines.put(zyt.allocator, "🍋TRACE_FALLBACK", trace_fallback);
        }
        { // 🍋TRACE_INPUT
            const trace_input = try std.fmt.allocPrint(
                zyt.allocator,
                \\if (yyact < YY_MIN_REDUCE) {{
                \\            {s}.print("{{s}}Input '{{s}}' in state {{d}}\n",
                \\                .{{ yyTracePrompt, yyTokenName[yymajor], yyact }},
                \\            ) catch {{}};
                \\        }} else {{
                \\            {s}.print("{{s}}Input '{{s}}' with pending reduce {{d}}\n",
                \\               .{{ yyTracePrompt, yyTokenName[yymajor], yyact - YY_MIN_REDUCE }},
                \\            ) catch {{}};
                \\        }}
            ,
                .{ trace, trace },
            );
            errdefer zyt.allocator.free(trace_input);
            try zyt.defines.put(zyt.allocator, "🍋TRACE_INPUT", trace_input);
        }
        { // 🍋TRACE_POP
            const trace_pop = try std.fmt.allocPrint(
                zyt.allocator,
                \\{s}.print("{{s}}Popping {{s}}\n",
                \\            .{{ yyTracePrompt, yyTokenName[yytos[0].major] }},
                \\        ) catch {{}};
            ,
                .{trace},
            );
            errdefer zyt.allocator.free(trace_pop);
            try zyt.defines.put(zyt.allocator, "🍋TRACE_POP", trace_pop);
        }
        { // 🍋TRACE_REDUCE
            const trace_reduce = try std.fmt.allocPrint(
                zyt.allocator,
                \\const yysize = yyRuleInfoNRhs[yyruleno];
                \\                if (yysize == 0) {{
                \\                    {s}.print("{{s}}Reduce {{d}} [{{s}}]{{s}}, pop back to state {{d}}\n",
                \\                        .{{ yyTracePrompt,
                \\                           yyruleno,
                \\                           yyRuleName[yyruleno],
                \\                           if (yyruleno < YYNRULE_WITH_ACTION) "" else " without external action",
                \\                           (yypParser.tos - @abs(yysize))[0].stateno,
                \\                        }},
                \\                    ) catch {{}};
                \\                }} else {{
                \\                   {s}.print("{{s}}Reduce {{d}} [{{s}}]{{s}}\n",
                \\                      .{{ yyTracePrompt, yyruleno, yyRuleName[yyruleno],
                \\                          if (yyruleno < YYNRULE_WITH_ACTION) "" else " without external action" }},
                \\                   ) catch {{}};
                \\                }}
            ,
                .{ trace, trace },
            );
            errdefer zyt.allocator.free(trace_reduce);
            try zyt.defines.put(zyt.allocator, "🍋TRACE_REDUCE", trace_reduce);
        }
        { // 🍋TRACE_RETURN
            const trace_return = try std.fmt.allocPrint(
                zyt.allocator,
                \\var cDiv: u8 = '[';
                \\        {s}.print("{{s}}Return. Stack=", .{{yyTracePrompt}}) catch {{}};
                \\        var yy_i = yypParser.stack + 1;
                \\        while (@intFromPtr(yy_i) <= @intFromPtr(yypParser.tos)) : ( yy_i += 1) {{
                \\            {s}.print("{{u}}{{s}}", .{{ cDiv, yyTokenName[yy_i[0].major] }}) catch {{}};
                \\            cDiv = ' ';
                \\        }}
                \\        {s}.writeAll("]\n") catch {{}};
            ,
                .{ trace, trace, trace },
            );
            errdefer zyt.allocator.free(trace_return);
            try zyt.defines.put(zyt.allocator, "🍋TRACE_RETURN", trace_return);
        }
        { // 🍋TRACE_SHIFT
            const trace_shift = try std.fmt.allocPrint(
                zyt.allocator,
                \\if (yyNewState < YYNSTATE) {{
                \\            {s}.print("{{s}}{{s}} '{{s}}', go to state {{d}}\n",
                \\                .{{ yyTracePrompt, zTag, yyTokenName[yypParser.tos[0].major], yyNewState }},
                \\            ) catch {{}};
                \\        }} else {{
                \\            {s}.print("{{s}}{{s}} '{{s}}', pending reduce {{d}}\n",
                \\               .{{ yyTracePrompt, zTag, yyTokenName[yypParser.tos[0].major], yy_sint(yyNewState) - YY_MIN_REDUCE }},
                \\            ) catch {{}};
                \\        }}
            ,
                .{ trace, trace },
            );
            errdefer zyt.allocator.free(trace_shift);
            try zyt.defines.put(zyt.allocator, "🍋TRACE_SHIFT", trace_shift);
        }

        { // 🍋TRACE_STACK_OVERFLOW
            const trace_stack_overflow = try std.fmt.allocPrint(
                zyt.allocator,
                \\{s}.print("{{s}}Stack Overflow!\n", .{{yyTracePrompt}}) catch {{}};
            ,
                .{trace},
            );
            errdefer zyt.allocator.free(trace_stack_overflow);
            try zyt.defines.put(zyt.allocator, "🍋TRACE_STACK_OVERFLOW", trace_stack_overflow);
        }

        { // 🍋TRACE_SYNTAX_ERROR
            const trace_syntax_error = try std.fmt.allocPrint(
                zyt.allocator,
                \\{s}.print("{{s}}Syntax Error!\n", .{{yyTracePrompt}}) catch {{}};
            ,
                .{trace},
            );
            errdefer zyt.allocator.free(trace_syntax_error);
            try zyt.defines.put(zyt.allocator, "🍋TRACE_SYNTAX_ERROR", trace_syntax_error);
        }

        { // 🍋TRACE_WILDCARD
            const trace_wildcard = try std.fmt.allocPrint(
                zyt.allocator,
                \\{s}.print("{{s}}WILDCARD {{s}} => {{s}}\n",
                \\                            .{{ yyTracePrompt, yyTokenName[yy_lookahead], yyTokenName[YYWILDCARD] }}) catch {{}};
            ,
                .{trace},
            );
            errdefer zyt.allocator.free(trace_wildcard);
            try zyt.defines.put(zyt.allocator, "🍋TRACE_WILDCARD", trace_wildcard);
        }
    }
    var in = try macroReplace(zyt, in_template);
    // We bump 'in' forward (following the C code) so we need to hold on to the
    // head so we can dispose of it:
    const in_head = in;
    defer {
        zyt.allocator.free(in_head);
    }
    try out.print(
        \\//! This file is automatically generated by Zitron from input grammar
        \\//! source file "{s}"
    , .{zyt.filename});
    lineno += 1;
    if (zyt.opt.nDefineUsed == 0) {
        try out.writeAll(".\n//!\n");
        lineno += 2;
    } else {
        try out.writeAll("\n//! with these options:\n//!\n");
        lineno += 3;
        for (0..zyt.opt.azDefine.len) |i| {
            if (!zyt.opt.bDefineUsed[i]) continue;
            try out.print("//!   -D={s}\n", .{zyt.opt.azDefine[i]});
            lineno += 1;
        }
        try out.writeAll("//!\n\n");
        lineno += 2;
    }

    // If the first %include directive begins with a top-level doc comment,
    // then skip over the header comment of the template file.
    {
        var include = zyt.include;
        var i: usize = 0;
        var nl_skip: usize = 0;
        while (i < include.len and isSpace(include[i])) : (i += 1) {
            if (include[i] == '\n') {
                nl_skip = i + 1;
            }
        }
        include = include[nl_skip..];
        if (include.len > 3 and include[0] == '/' and include[1] == '/' and include[2] == '!') {
            tplt_skip_header(&in);
        } else {
            try tplt_xfer(zyt.name, &in, out, &lineno);
        }
        // Generate the include code, if any.
        try tplt_print(out, zyt, include, &lineno);
    }
    try out.writeAll("// zig fmt: off\n");
    lineno += 1;
    try tplt_xfer(zyt.name, &in, out, &lineno);
    if (zyt.opt.enum_file) {
        const t_name = zyt.defines.get("🍋TOKEN_ENUM").?;
        try out.print(
            "pub const {s} = @import(\"{s}.zig\").{s};\n",
            .{ t_name, t_name, t_name },
        );
        lineno += 1;
    } else {
        // Generate token enum
        try print_token_enum(zyt, out, &lineno);
    }
    try tplt_xfer(zyt.name, &in, out, &lineno);

    // Generate the defines
    // zig fmt: off
    var szCodeType: u8 = 0;
    var szActionType: u8 = 0;
    try out.print("const YYCODETYPE = {s};\n", .{minimum_size_type(0, zyt.nsymbol, &szCodeType, true)}); lineno += 1;
    try out.print("const YYNOCODE = {d};\n", .{zyt.nsymbol}); lineno += 1;
    try out.print("const YYACTIONTYPE = {s};\n", .{minimum_size_type(0, zyt.maxAction, &szActionType, false)}); lineno += 1;
    if (zyt.wildcard) |wild| {
        try out.print("const YY_HASWILDCARD = true;\nconst YYWILDCARD = {d};\n", .{wild.index});
    } else {
        try out.writeAll("const YY_HASWILDCARD = false;\nconst YYWILDCARD: void = {};\n");
    }
    lineno += 2;
    try print_stack_union(out, zyt, &lineno);
    try out.writeAll("const YYSTACKDEPTH = ");
    if (zyt.stacksize.len > 0) {
        try out.print("{s};\n", .{zyt.stacksize}); lineno += 1;
    } else {
        try out.writeAll("256;\n"); lineno += 1;
    }
    if (zyt.errsym) |errsym| if (errsym.useCnt > 0) {
        try out.writeAll("const YYHAS_ERRORSYMBOL = true;\n"); lineno += 1;
        try out.print("const YYERRORSYMBOL = {d};\n", .{errsym.index}); lineno += 1;
        try out.print("const YYERRSYMDT = @FieldType(YYMINORTYPE, \"{s}\");\n", .{errsym.dttag}); lineno += 1;
    } else {} else {
        try out.writeAll("const YYHAS_ERRORSYMBOL = false;\n"); lineno += 1;
    }
    // TODO: need %trace_writer directive
    try out.writeAll("const YY_TRACE = false;\n"); lineno += 1;
    try out.writeAll("const YYFALLBACK = ");
    if (zyt.has_fallback) {
        try out.writeAll("true");
    } else {
        try out.writeAll("false");
    }
    try out.writeAll(";\n"); lineno += 1;
    // zig fmt: on
    // Compute the action table, but do not output it yet.  The action
    // table must be computed before generating the YYNSTATE macro because
    // we need to know how many states can be eliminated.
    const pActtab = try Compute_actiontable(zyt);
    defer pActtab.destroy();
    // Mark rules that are actually used for reduce actions after all
    // optimizations have been applied
    {
        var m_rp: ?*Rule = zyt.rule;
        while (m_rp) |rp| : (m_rp = rp.next) rp.doesReduce = false;
        for (0..zyt.nxstate) |i| {
            var m_ap: ?*Action = zyt.sorted[i].ap;
            while (m_ap) |ap| : (m_ap = ap.next) {
                if (ap.type == .reduce or ap.type == .shiftreduce) {
                    ap.x.rp.?.doesReduce = true;
                }
            }
        }
    }
    // zig fmt: off
    {
        // Finish rendering the constants now that the action table has
        // been computed
        try out.print("const YYNSTATE =             {d};\n", .{zyt.nxstate}); lineno += 1;
        try out.print("const YYNRULE =              {d};\n", .{zyt.nrule}); lineno += 1;
        try out.print("const YYNRULE_WITH_ACTION =  {d};\n", .{zyt.nruleWithAction}); lineno += 1;
        try out.print("const YYNTOKEN =             {d};\n", .{zyt.nterminal}); lineno += 1;
        try out.print("const YY_MAX_SHIFT =         {d};\n", .{zyt.nxstate - 1}); lineno += 1;
        var i = zyt.minShiftReduce;
        try out.print("const YY_MIN_SHIFTREDUCE =   {d};\n", .{i}); lineno += 1;
        i += zyt.nrule;
        try out.print("const YY_MAX_SHIFTREDUCE =   {d};\n", .{i - 1}); lineno += 1;
        try out.print("const YY_ERROR_ACTION =      {d};\n", .{zyt.errAction}); lineno += 1;
        try out.print("const YY_ACCEPT_ACTION =     {d};\n", .{zyt.accAction}); lineno += 1;
        try out.print("const YY_NO_ACTION =         {d};\n", .{zyt.noAction}); lineno += 1;
        try out.print("const YY_MIN_REDUCE =        {d};\n", .{zyt.minReduce}); lineno += 1;
        i = zyt.minReduce + zyt.nrule;
        try out.print("const YY_MAX_REDUCE =        {d};\n", .{i - 1}); lineno += 1;
    }
    // zig fmt: on
    {
        // Minimum and maximum rule values which have a destructor
        var min: usize = 0;
        var max: usize = 0;
        for (0..zyt.nsymbol) |i| {
            const sp = zyt.symbols[i];
            if (sp.type != .terminal and sp.destructor.len > 0) {
                if (min == 0 or sp.index < min) min = sp.index;
                if (sp.index > max) max = sp.index;
            }
        }
        if (zyt.tokendest.len > 0) min = 0;
        if (zyt.vardest.len > 0) max = zyt.nsymbol - 1;
        try out.print(
            "const YY_HAS_TOKEN_DESTRUCTOR = {};\n",
            .{zyt.tokendest.len > 0},
        );
        lineno += 1;
        try out.print("const YY_MIN_DSTRCTR =       {d};\n", .{min});
        lineno += 1;
        try out.print("const YY_MAX_DSTRCTR =       {d};\n", .{max});
        lineno += 1;
        try tplt_xfer(zyt.name, &in, out, &lineno);
    }

    // Now output the action table and its associates:
    //
    //  yy_action[]        A single table containing all actions.
    //  yy_lookahead[]     A table containing the lookahead for each entry in
    //                     yy_action.  Used to detect hash collisions.
    //  yy_shift_ofst[]    For each state, the offset into yy_action for
    //                     shifting terminals.
    //  yy_reduce_ofst[]   For each state, the offset into yy_action for
    //                     shifting non-terminals after a reduce.
    //  yy_default[]       Default action for each state.

    // Output the yy_action table
    {
        zyt.nactiontab = pActtab.actionSize();
        const n = zyt.nactiontab;
        zyt.tablesize += n * szActionType;
        try out.print("const YY_ACTTAB_COUNT = {d};\n", .{n});
        lineno += 1;
        try out.writeAll("// zig fmt: off\n");
        lineno += 1;
        try out.writeAll("const yy_action: [YY_ACTTAB_COUNT]YYACTIONTYPE  = .{\n");
        lineno += 1;
        var i: usize = 0;
        var j: usize = 0;
        var j_row: usize = 0;
        while (i < n) : (i += 1) {
            var action = pActtab.yyaction(i);
            if (action < 0) action = @intCast(zyt.noAction);
            // This bit of brain-damage is to prevent a width-specified
            // positive signed value from getting a spurious `+`.  Whyyyy
            if (action >= 0) {
                try out.print(" {d: >4},", .{uint(action)});
            } else {
                try out.print(" {d: >4},", .{action});
            }
            if (j == 9 or i == n - 1) {
                try out.print(" // {d: >5}\n", .{j_row});
                lineno += 1;
                j_row = i + 1;
                j = 0;
            } else {
                j += 1;
            }
        }
        try out.writeAll("};\n");
        lineno += 1;
    }

    // Output the yy_lookahead table
    {
        zyt.nlookaheadtab = pActtab.lookaheadSize();
        const n = zyt.nlookaheadtab;
        const nLookAhead = zyt.nterminal + zyt.nactiontab;
        zyt.tablesize += nLookAhead * szCodeType;
        try out.print("const yy_lookahead: [{d}]YYCODETYPE = .{{\n", .{nLookAhead});
        lineno += 1;
        var i: usize = 0;
        var j: usize = 0;
        var j_row: usize = 0;
        while (i < n) : (i += 1) {
            var la = pActtab.yylookahead(i);
            if (la < 0) la = @intCast(zyt.nsymbol);
            try out.print(" {d: >4},", .{uint(la)});
            if (j == 9 or i == n - 1) {
                try out.print(" // {d: >5}\n", .{j_row});
                lineno += 1;
                j_row = i + 1;
                j = 0;
            } else {
                j += 1;
            }
        }
        // Add extra entries to the end of the yy_lookahead[] table so that
        // yy_shift_ofst[]+iToken will always be a valid index into the array,
        // even for the largest possible value of yy_shift_ofst[] and iToken.

        while (i < nLookAhead) {
            try out.print(" {d: >4},", .{zyt.nterminal});
            if (j == 9 or i == nLookAhead - 1) {
                try out.print(" // {d: >5}\n", .{j_row});
                j = 0;
                j_row = i + 1;
                lineno += 1;
            } else {
                j += 1;
            }
            i += 1;
        }
        if (j > 0) {
            try out.writeByte('\n');
            lineno += 1;
        }
        try out.writeAll("};\n");
        lineno += 1;
    }

    // Output the yy_shift_ofst[] table
    {
        var n = zyt.nxstate;
        while (n > 0 and zyt.sorted[n - 1].iTknOfst == NO_OFFSET) : (n -= 1) {}
        try out.print("const YY_SHIFT_COUNT =    {d};\n", .{n - 1});
        lineno += 1;
        try out.print("const YY_SHIFT_MIN =      {d};\n", .{pActtab.mnTknOfst});
        lineno += 1;
        try out.print("const YY_SHIFT_MAX =      {d};\n", .{pActtab.mxTknOfst});
        lineno += 1;
        var sz: u8 = 0;
        try out.print(
            "const yy_shift_ofst: [{d}]{s} = .{{\n",
            .{ n, minimum_size_type(pActtab.mnTknOfst, zyt.nterminal + zyt.nactiontab, &sz, false) },
        );
        lineno += 1;
        zyt.tablesize += n * sz;
        var i: usize = 0;
        var j: usize = 0;
        var j_row: usize = 0;
        while (i < n) : (i += 1) {
            const stp = zyt.sorted[i];
            var ofst = stp.iTknOfst;
            if (ofst == NO_OFFSET) ofst = @intCast(zyt.nactiontab);
            if (ofst >= 0) {
                try out.print(" {d: >4},", .{uint(ofst)});
            } else {
                try out.print(" {d: >4},", .{ofst});
            }
            if (j == 9 or i == n - 1) {
                try out.print(" // {d: >5}\n", .{j_row});
                lineno += 1;
                j_row = i + 1;
                j = 0;
            } else {
                j += 1;
            }
        }
        try out.writeAll("};\n");
        lineno += 1;
    }

    // Output the yy_reduce_ofst[] table
    {
        var n = zyt.nxstate;
        while (n > 0 and zyt.sorted[n - 1].iNtOfst == NO_OFFSET) : (n -= 1) {}

        try out.print("const YY_REDUCE_COUNT = {d};\n", .{n - 1});
        lineno += 1;
        try out.print("const YY_REDUCE_MIN =   {d};\n", .{pActtab.mnNtOfst});
        lineno += 1;
        try out.print("const YY_REDUCE_MAX =   {d};\n", .{pActtab.mxNtOfst});
        lineno += 1;
        var sz: u8 = 0;
        try out.print(
            "const yy_reduce_ofst: [{d}]{s}  = .{{\n",
            .{ n, minimum_size_type(pActtab.mnNtOfst - 1, @intCast(pActtab.mxNtOfst), &sz, false) },
        );
        lineno += 1;
        zyt.tablesize += n * sz;
        var i: usize = 0;
        var j: usize = 0;
        var j_row: usize = 0;
        while (i < n) : (i += 1) {
            const stp = zyt.sorted[i];
            var ofst = stp.iNtOfst;
            if (ofst == NO_OFFSET) ofst = pActtab.mnNtOfst - 1;
            if (ofst >= 0) {
                try out.print(" {d: >4},", .{uint(ofst)});
            } else {
                try out.print(" {d: >4},", .{ofst});
            }
            if (j == 9 or i == n - 1) {
                try out.print(" // {d: >5}\n", .{j_row});
                lineno += 1;
                j_row = i + 1;
                j = 0;
            } else {
                j += 1;
            }
        }
        try out.writeAll("};\n");
        lineno += 1;
    }

    // Output the default action table
    try out.print("const yy_default: [{d}]YYACTIONTYPE = .{{\n", .{zyt.nxstate});
    lineno += 1;
    {
        const n = zyt.nxstate;
        zyt.tablesize += n * szActionType;
        var i: usize = 0;
        var j: usize = 0;
        var j_row: usize = 0;
        while (i < n) : (i += 1) {
            const stp = zyt.sorted[i];
            if (stp.iDfltReduce < 0) {
                try out.print(" {d: >4},", .{zyt.errAction});
            } else {
                try out.print(" {d: >4},", .{uint(stp.iDfltReduce) + zyt.minReduce});
            }
            if (j == 9 or i == n - 1) {
                try out.print(" // {d: >5}\n", .{j_row});
                lineno += 1;
                j_row = i + 1;
                j = 0;
            } else {
                j += 1;
            }
        }
        try out.writeAll("};\n");
        lineno += 1;
        try tplt_xfer(zyt.name, &in, out, &lineno);
    }

    // Generate the table of fallback tokens.
    if (zyt.has_fallback) {
        const max = zyt.nterminal;
        //   /* 2019-08-28:  Generate fallback entries for every token to avoid
        //   ** having to do a range check on the index */
        //   /* while( mx>0 && lemp->symbols[mx]->fallback==0 ){ mx--; } */
        zyt.tablesize += (max) * szCodeType;
        for (0..max) |i| {
            const sp = zyt.symbols[i];
            if (sp.fallback) |fallback| {
                try out.print("  {d: >3},  // {s: >10} => {s} \n", .{ fallback.index, sp.name, fallback.name });
            } else {
                try out.print("    0,  // {s: >10} => nothing \n", .{sp.name});
            }
            lineno += 1;
        }
    }
    try tplt_xfer(zyt.name, &in, out, &lineno);

    // Generate a table containing the symbolic name of every symbol
    {
        var maxsym: usize = 0;
        for (0..zyt.nsymbol) |i| {
            maxsym = @max(maxsym, zyt.symbols[i].name.len);
        }
        for (0..zyt.nsymbol) |i| {
            try out.print("   \"{s}\",  ", .{zyt.symbols[i].name});
            try out.splatByteAll(' ', maxsym - zyt.symbols[i].name.len);
            try out.print("// {d: >4}\n", .{i});
            lineno += 1;
        }
        try tplt_xfer(zyt.name, &in, out, &lineno);
    }
    {
        // /* Generate a table containing a text string that describes every
        // ** rule in the rule set of the grammar.  This information is used
        // ** when tracing REDUCE actions.
        var i: usize = 0;
        // TODO: Clean up the comment numbering here, as above
        var m_rp: ?*Rule = zyt.rule;
        while (m_rp) |rp| : (m_rp = rp.next) {
            dbgassert(rp.iRule == i);
            try out.writeAll("    \"");
            try writeRuleText(out, rp);
            try out.print("\", // {d: >3} \n", .{i});
            lineno += 1;
            i += 1;
        }
        try tplt_xfer(zyt.name, &in, out, &lineno);
    }

    // Generate code which executes every time a symbol is popped from
    // the stack while processing errors or while destroying the parser.
    // (In other words, generate the %destructor actions)
    //
    if (zyt.tokendest.len > 0) {
        var once = true;
        for (0..zyt.nsymbol) |i| {
            const sp = zyt.symbols[i];
            if (sp.type != .terminal) continue;
            if (once) {
                try out.writeAll("        // TERMINAL Destructor\n");
                lineno += 1;
                once = false;
            }
            try out.print("        {d}, // {s}\n", .{ sp.index, sp.name });
            lineno += 1;
        }
        var j: usize = 0;
        while (j < zyt.nsymbol and zyt.symbols[j].type != .terminal) : (j += 1) {}
        if (j < zyt.nsymbol) {
            try emit_destructor_code(out, zyt.symbols[j], zyt, &lineno);
        }
    }
    if (zyt.vardest.len > 0) {
        var once = true;
        var dflt_sp: ?*Symbol = null;
        for (0..zyt.nsymbol) |i| {
            const sp = zyt.symbols[i];
            if (sp.type == .terminal or sp.index == 0 or sp.destructor.len > 0) continue;
            if (once) {
                try out.writeAll("        // Default NON-TERMINAL Destructor */\n");
                lineno += 1;
                once = false;
            }
            try out.print("    {d}, // {s} \n", .{ sp.index, sp.name });
            lineno += 1;
            dflt_sp = sp;
        }
        if (dflt_sp) |dflt| {
            try emit_destructor_code(out, dflt, zyt, &lineno);
        }
    }
    for (0..zyt.nsymbol) |i| {
        const sp = zyt.symbols[i];
        if (sp.type == .terminal or sp.destructor.len == 0) continue;
        if (p_check1) {
            dprint(
                "destructor: {s} d_line {?} dtnum {d}, destructor? {s}\n",
                .{ sp.name, sp.destLineno, sp.dtnum, if (sp.destructor.len > 0) "yes" else "no" },
            );
        }
        if (sp.destLineno == null) continue; //  Already emitted
        try out.print("        {d}, // {s} \n", .{ sp.index, sp.name });
        lineno += 1;
        if (zyt.opt.unbundle) {
            try emit_destructor_code(out, sp, zyt, &lineno);
            continue;
        }
        // Combine duplicate destructors into a single case
        var j = i + 1;
        while (j < zyt.nsymbol) : (j += 1) {
            const sp2 = zyt.symbols[j];
            if (sp2.type != .terminal and
                sp2.dtnum == sp.dtnum and
                sp2.destructor.len > 0 and mem.eql(u8, sp.destructor, sp2.destructor))
            {
                try out.print("        {d}, // {s} \n", .{ sp2.index, sp2.name });
                lineno += 1;
                sp2.destLineno = null; // Avoid emitting this destructor again */
            }
        }
        try emit_destructor_code(out, sp, zyt, &lineno);
    }
    // NOTE: This is pure fudge, we have a dropped line between destructor
    // and reduce emits. ¯\_(ツ)_/¯
    lineno += 1;
    try tplt_xfer(zyt.name, &in, out, &lineno);
    // Generate code which executes whenever the parser stack overflows
    try tplt_print(out, zyt, zyt.overflow, &lineno);
    try tplt_xfer(zyt.name, &in, out, &lineno);

    //
    // Generate the tables of rule information.  yyRuleInfoLhs[] and
    // yyRuleInfoNRhs[].
    //
    // Note: This code depends on the fact that rules are numbered
    // sequentially beginning with 0.
    {
        var m_rp: ?*Rule = zyt.rule;
        var i: usize = 0; // zig fmt: off
        while (m_rp) |rp| : ({m_rp = rp.next; i += 1; }) {
            try out.print("  {d: >4},  // ({d}) ", .{ rp.lhs.index, i });
            try rule_print(out, rp);
            try out.writeAll( "\n" ); lineno += 1;
        }
        try tplt_xfer(zyt.name, &in, out, &lineno);
        i = 0; m_rp = zyt.rule;

        while (m_rp) |rp| : ({m_rp = rp.next; i += 1; }) {
            if (rp.rhs.len == 0) {
                try out.print("  {d: >3},", .{rp.rhs.len});
            } else {
                try out.print("  {d: >3},", .{-sint(rp.rhs.len)});
            }
            try out.print("  // ({d}) ", .{i});
            try rule_print(out, rp);
            try out.writeAll("\n"); lineno += 1;
        }
        try tplt_xfer(zyt.name, &in, out, &lineno);
            // zig fmt: on
    }

    // Generate code which execution during each REDUCE action
    {
        var minor_type = false;
        var m_rp: ?*Rule = zyt.rule;
        while (m_rp) |rp| : (m_rp = rp.next) {
            const did = try translate_code(zyt, rp);
            minor_type = minor_type or did;
        }
        // First output rules other than the default: rule
        m_rp = zyt.rule;
        rules: while (m_rp) |rp| : (m_rp = rp.next) {
            if (rp.codeEmitted) continue :rules;
            if (rp.noCode) {
                // No C code actions, so this will be part of the "default:" rule
                continue :rules;
            }
            try out.print("        {d}, // ", .{rp.iRule});
            try writeRuleText(out, rp);
            try out.writeByte('\n');
            lineno += 1;
            if (!zyt.opt.unbundle) {
                var m_rp2: ?*Rule = rp.next; // Other rules with the same action
                while (m_rp2) |rp2| : (m_rp2 = rp2.next) {
                    if (rp.code.ptr == rp2.code.ptr and
                        rp.codePrefix.ptr == rp2.codePrefix.ptr and
                        rp.codeSuffix.ptr == rp2.codeSuffix.ptr)
                    {
                        if (p_check1) {
                            dprint("case: merging rp2 {d} with rp {d}\n", .{ rp2.iRule, rp.iRule });
                        }
                        try out.print("        {d}, // ", .{rp2.iRule});
                        try writeRuleText(out, rp2);
                        try out.writeByte('\n');
                        lineno += 1;
                        rp2.codeEmitted = true;
                    }
                }
            }
            try emit_code(out, rp, zyt, &lineno);
            rp.codeEmitted = true;
        }
    }
    // Finally, output the default: rule.  We choose as the default: all
    // empty actions.

    try out.writeAll("        else => {\n");
    lineno += 1;
    {
        var m_rp: ?*Rule = zyt.rule;
        while (m_rp) |rp| : (m_rp = rp.next) {
            if (rp.codeEmitted) continue;
            dbgassert(rp.noCode);
            if (rp.neverReduce) {
                try out.print("            yy_assert(yyruleno != {d}); // ({d}) ", .{ rp.iRule, rp.iRule });
                try writeRuleText(out, rp);
                try out.writeAll(" (NEVER REDUCES)\n");
                lineno += 1;
            } else if (rp.doesReduce) {
                try out.writeAll("            // ");
                try writeRuleText(out, rp);
                try out.writeByte('\n');
                lineno += 1;
            } else {
                try out.print("            yy_assert(yyruleno != {d}); // ({d}) ", .{ rp.iRule, rp.iRule });
                try writeRuleText(out, rp);
                try out.writeAll(" (OPTIMIZED OUT) \n");
                lineno += 1;
            }
        }
    }
    try out.writeAll("        },\n");
    lineno += 1;
    try tplt_xfer(zyt.name, &in, out, &lineno);

    // Generate code which executes if a parse fails
    try tplt_print(out, zyt, zyt.failure, &lineno);
    try tplt_xfer(zyt.name, &in, out, &lineno);

    // Generate code which executes when a syntax error occurs
    try tplt_print(out, zyt, zyt.@"error", &lineno);
    try tplt_xfer(zyt.name, &in, out, &lineno);

    // Generate code which executes when the parser accepts its input
    try tplt_print(out, zyt, zyt.accept, &lineno);
    try tplt_xfer(zyt.name, &in, out, &lineno);

    // Append any addition code the user desires.
    try tplt_print(out, zyt, zyt.extracode, &lineno);

    if (zyt.opt.sql_flag) {
        const m_sql_fh = try file_open(zyt, ".sql", false, .{});
        if (m_sql_fh) |fh| {
            defer fh.close(zyt.io);
            var out_buffer: [4096]u8 = undefined;
            var f_writer = fh.writer(zyt.io, &out_buffer);
            const sql = &f_writer.interface;
            try ReportSql(zyt, pActtab, sql);
            try sql.flush();
        } else {} // No file handle
    }
}

/// Generate a header file for the parser
fn ReportHeader(zyt: *Zitron) !void {
    // The original opens the file to read and checks if anything
    // has changed, only then does it write.  We're just going to
    // do it.
    const filename = if (zyt.opt.output_file.len > 0) zyt.opt.output_file else zyt.filename;
    const dir = if (zyt.opt.output_directory.len > 0)
        zyt.opt.output_directory
    else if (std.mem.lastIndexOfScalar(u8, filename, '/')) |i|
        filename[0..i]
    else
        ".";
    const tok_filename = try std.fmt.allocPrint(
        zyt.allocator,
        "{s}/{s}.zig",
        .{ dir, zyt.defines.get("🍋TOKEN_ENUM").? },
    );
    defer zyt.allocator.free(tok_filename);
    const m_fh = try open_file(zyt, tok_filename, .{});
    if (m_fh) |fh| {
        defer fh.close(zyt.io);
        var out_buffer: [4096]u8 = undefined;
        var f_writer = fh.writer(zyt.io, &out_buffer);
        const out = &f_writer.interface;
        var line_dummy: usize = 0;
        try print_token_enum(zyt, out, &line_dummy);
        try out.flush();
    } else {
        std.debug.print("did not open token file\n", .{});
    }
}

/// The God Object handling state for the parser generator.
const Zitron = struct {
    /// Allocator
    allocator: Allocator,
    /// Command-line options
    opt: Options,
    /// Table of states sorted by state number
    sorted: []*State,
    /// List of all rules
    rule: *Rule,
    /// First rule
    startRule: *Rule,
    /// Defines map
    defines: std.StringHashMapUnmanaged([]const u8),
    /// Number of states
    nstate: u32,
    /// nstate with tail degenerate states removed
    nxstate: u32,
    /// Number of rules
    nrule: u32,
    /// Number of rules with actions
    nruleWithAction: u32,
    /// Number of terminal and nonterminal symbols
    nsymbol: u32,
    /// Number of terminal symbols
    nterminal: u32,
    /// Minimum shift-reduce action value
    minShiftReduce: u32,
    /// Error action value
    errAction: u32,
    /// Accept action value
    accAction: u32,
    /// No-op action value
    noAction: u32,
    /// Minimum reduce action
    minReduce: u32,
    /// Maximum action value of any kind
    maxAction: u32,
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
    /// Type of parser error set
    error_type: []u8,
    /// Code appended to the generated file
    extracode: []u8,
    /// Code to execute to destroy token data
    tokendest: []u8,
    /// Code for the default non-terminal destructor
    vardest: []u8,
    /// Name of the input file
    filename: []const u8,
    /// Name of the current output file
    outname: []const u8,
    /// Custom name for TokenKind enum type
    token_enum: []u8,
    /// Custom backing integer for TokenKind enum type
    token_enum_integer: []u8,
    /// Variable containing an Io.Writer for tracing
    trace_writer: []u8,
    /// Process IO handle for file and stdio operations
    io: std.Io,
    /// Number of parse conflicts
    nconflict: u32,
    /// Number of entries in the yy_action[] table
    nactiontab: u32,
    ///  Number of entries in yy_lookahead[]
    nlookaheadtab: u32,
    /// Total table size of all tables in bytes
    tablesize: u32,
    /// Show preprocessor output on stdout
    printPreprocessed: bool,
    /// True if any %fallback is seen in the grammar
    has_fallback: bool,
    /// True if #line statements should be printed
    linenosflag: bool,
    /// Command-line arguments
    argv: []const [:0]const u8,

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

    pub const empty: Zitron = .{
        .allocator = undefined,
        .opt = .{},
        .sorted = &.{},
        .rule = undefined,
        .startRule = undefined,
        .defines = .empty,
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
        .token_enum = &.{},
        .token_enum_integer = &.{},
        .trace_writer = &.{},
        .io = undefined,
        .vartype = &.{},
        .start = &.{},
        .stacksize = &.{},
        .include = &.{},
        .@"error" = &.{},
        .overflow = &.{},
        .failure = &.{},
        .accept = &.{},
        .error_type = &.{},
        .extracode = &.{},
        .tokendest = &.{},
        .vardest = &.{},
        .filename = "",
        .outname = "",
        .tokentype = &.{},
        .nconflict = 0,
        .nactiontab = 0,
        .nlookaheadtab = 0,
        .tablesize = 0,
        .printPreprocessed = false,
        .has_fallback = false,
        .linenosflag = false,
        .argv = &.{},
    };

    pub fn create(allocator: Allocator) !*Zitron {
        const gp = try allocator.create(Zitron);
        errdefer allocator.destroy(gp);
        gp.* = .empty;
        gp.allocator = allocator;
        gp.sorted = try allocator.alloc(*State, 0);
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
        gp.error_type = try allocator.alloc(u8, 0);
        errdefer allocator.free(gp.error_type);
        gp.extracode = try allocator.alloc(u8, 0);
        errdefer allocator.free(gp.extracode);
        gp.tokendest = try allocator.alloc(u8, 0);
        errdefer allocator.free(gp.tokendest);
        gp.vardest = try allocator.alloc(u8, 0);
        errdefer allocator.free(gp.vardest);
        gp.token_enum = try allocator.alloc(u8, 0);
        errdefer allocator.free(gp.token_enum);
        gp.token_enum_integer = try allocator.alloc(u8, 0);
        errdefer allocator.free(gp.token_enum_integer);
        gp.trace_writer = try allocator.alloc(u8, 0);
        errdefer allocator.free(gp.trace_writer);
        gp.argv = undefined; // populated by std.process.argsAlloc.
        return gp;
    }

    pub fn destroy(gp: *Zitron, allocator: Allocator) void {
        var m_rp: ?*Rule = gp.rule;
        var rp_next = m_rp;
        while (m_rp) |rp| : (m_rp = rp_next) {
            rp_next = rp.next;
            rp.destroy(allocator);
        }
        var d_iter = gp.defines.valueIterator();
        while (d_iter.next()) |v| {
            allocator.free(v.*);
        }
        gp.defines.deinit(allocator);
        // allocator.free(gp.symbols);
        // allocator.free(gp.sorted);
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
        allocator.free(gp.error_type);
        allocator.free(gp.extracode);
        allocator.free(gp.tokendest);
        allocator.free(gp.token_enum);
        allocator.free(gp.token_enum_integer);
        allocator.free(gp.trace_writer);
        allocator.free(gp.vardest);
        allocator.free(gp.outname);
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
    lookahead: int,
    /// Action to take on the given lookahead
    action: int,

    pub const empty: LookaheadAction = .{ .lookahead = -1, .action = -1 };
};

const ActTable = struct {
    allocator: Allocator,
    ///  Number of used slots in aAction[]
    nAction: u32 = 0,
    /// Number of aAction slots in actual use
    nActionAlloc: u32 = 0,
    /// The yyaction[] table under construction
    aAction: []LookaheadAction = &.{},
    /// A single new transaction set
    aLookahead: []LookaheadAction = &.{},
    /// Minimum aLookahead[].lookahead
    mnLookahead: int = 0,
    /// Action associated with mnLookahead
    mnAction: int = 0,
    /// Maximum aLookahead[].lookahead
    mxLookahead: int = 0,
    ///  Used slots in aLookahead[]
    nLookahead: u32 = 0,
    ///  Slots allocated in aLookahead[]
    nLookaheadAlloc: u32 = 0,
    /// Number of terminal symbols
    nterminal: u32 = 0,
    /// total number of symbols
    nsymbol: u32 = 0,
    /// Minimum token offset
    mnTknOfst: i32 = 0,
    /// Maximum token offset
    mxTknOfst: i32 = 0,
    /// Minimum non-terminal offset
    mnNtOfst: i32 = 0,
    /// Maximum non-terminal offset
    mxNtOfst: i32 = 0,

    /// Create an action table
    pub fn create(allocator: Allocator, nsymbol: u32, nterminal: u32) !*ActTable {
        var tab = try allocator.create(ActTable);
        tab.* = .{ .allocator = allocator };
        errdefer allocator.destroy(tab);
        tab.nsymbol = nsymbol;
        tab.nterminal = nterminal;
        tab.allocator = allocator;
        return tab;
    }

    /// Free all action table memory.
    pub fn destroy(tab: *ActTable) void {
        tab.allocator.free(tab.aAction);
        tab.allocator.free(tab.aLookahead);
        tab.allocator.destroy(tab);
    }

    /// Return the number of entries in the yy_action table
    pub inline fn lookaheadSize(x: *const ActTable) u32 {
        return x.nAction;
    }

    /// The value for the N-th entry in yy_action
    pub inline fn yyaction(tab: *const ActTable, n: usize) i32 {
        return tab.aAction[n].action;
    }

    /// The value for the N-th entry in yy_lookahead
    pub inline fn yylookahead(tab: *const ActTable, n: usize) i32 {
        return tab.aAction[n].lookahead;
    }

    // [639]
    /// Add a new action to the current transaction set.
    ///
    /// This routine is called once for each lookahead for a particular
    /// state.
    pub fn action(tab: *ActTable, lookahead: u32, an_action: int) !void {
        if (tab.nLookahead >= tab.aLookahead.len) {
            tab.aLookahead = try tab.allocator.realloc(tab.aLookahead, tab.aLookahead.len + 25);
        }
        if (tab.nLookahead == 0) {
            tab.mxLookahead = @intCast(lookahead);
            tab.mnLookahead = @intCast(lookahead);
            tab.mnAction = an_action;
        } else {
            if (tab.mxLookahead < lookahead) tab.mxLookahead = @intCast(lookahead);
            if (tab.mnLookahead > lookahead) {
                tab.mnLookahead = @intCast(lookahead);
                tab.mnAction = an_action;
            }
        }
        tab.aLookahead[tab.nLookahead] = .{ .lookahead = @intCast(lookahead), .action = an_action };
        tab.nLookahead += 1;
    }

    /// NOTE: Used only in (obsolete) internal debug-reporting code.
    /// should be removed when the rest of that is.
    threadlocal var a_ct: usize = 0;

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
    pub fn insert(p: *ActTable, makeItSafe: bool) !int {
        if (p_check1) {
            a_ct += 1;
            dprint("({d}) Acttab: mnLookahead {d}\n", .{ a_ct, p.mnLookahead });
            dprint("Acttab: mxLookahead {d}\n", .{p.mxLookahead});
            dprint("Acttab: mnAction {d}\n", .{p.mnAction});
            dprint("Acttab: nAction {d}\n", .{p.nAction});
            dprint("Acttab: nLookahead {d}\n", .{p.nLookahead});
            if (makeItSafe) {
                dprint("make it safe.\n", .{});
            } else {
                dprint("make it zero.\n", .{});
            }
        }
        //  Make sure we have enough space to hold the expanded action table
        // in the worst case.  The worst case occurs if the transaction set
        // must be appended to the current action table.
        assert(p.nLookahead > 0);
        {
            const n = p.nsymbol + 1;
            if (p.nAction + n >= p.aAction.len) {
                const old_len = p.aAction.len;
                const new_cap = p.nAction + n + p.aAction.len + 20;
                p.aAction = try p.allocator.realloc(p.aAction, new_cap);
                @memset(p.aAction[old_len..], LookaheadAction.empty);
            }
        }
        // /* Scan the existing action table looking for an offset that is a
        // ** duplicate of the current transaction set.  Fall out of the loop
        // ** if and when the duplicate is found.
        // **
        // ** i is the index in p->aAction[] where p->mnLookahead is inserted.
        // */
        const end = if (makeItSafe) p.mnLookahead else 0;
        const act_items = p.aAction;
        const look_items = p.aLookahead;
        const pnAi: isize = @intCast(p.nAction);
        var i: isize = pnAi - 1;
        i_loop: while (i >= end) : (i -= 1) {
            if (act_items[uint(i)].lookahead == p.mnLookahead) {
                // All lookaheads and actions in the aLookahead[] transaction
                // must match against the candidate aAction[i] entry.
                if (act_items[uint(i)].action != p.mnAction) continue :i_loop;
                var j: usize = 0;
                j_loop: while (j < p.nLookahead) : (j += 1) {
                    const k: isize = look_items[j].lookahead - p.mnLookahead + i;
                    if (k < 0 or k >= p.nAction) break :j_loop;
                    if (look_items[j].lookahead != act_items[uint(k)].lookahead) break :j_loop;
                    if (look_items[j].action != act_items[uint(k)].action) break :j_loop;
                }
                if (j < p.nLookahead) continue :i_loop;

                // No possible lookahead value that is not in the aLookahead[]
                // transaction is allowed to match aAction[i]
                var n: i32 = 0;
                j = 0;
                j_check: while (j < p.nAction) : (j += 1) {
                    if (act_items[j].lookahead < 0) continue :j_check;
                    if (act_items[j].lookahead == cast(i32, j) + p.mnLookahead - i) n += 1;
                }

                if (n == p.nLookahead) {
                    break :i_loop; //An exact match is found at offset i
                }
            }
        }
        // If no existing offsets exactly match the current transaction, find an
        // an empty offset in the aAction[] table in which we can add the
        // aLookahead[] transaction.
        if (i < end) {
            // Look for holes in the aAction[] table that fit the current
            // aLookahead[] transaction.  Leave i set to the offset of the hole.
            // If no holes are found, i is left at p->nAction, which means the
            // transaction will be appended.
            i = if (makeItSafe) @intCast(p.mnLookahead) else 0;
            const mxsize = p.mxLookahead;
            const pActlen: isize = @intCast(p.aAction.len);
            i_loop: while (i < pActlen - mxsize) : (i += 1) {
                if (act_items[uint(i)].lookahead < 0) {
                    var j: usize = 0;
                    j_loop: while (j < p.nLookahead) : (j += 1) {
                        const k = look_items[j].lookahead - p.mnLookahead + i;
                        if (k < 0) break :j_loop;
                        if (act_items[uint(k)].lookahead >= 0) break :j_loop;
                    }
                    if (j < p.nLookahead) continue :i_loop;
                    j = 0;
                    j_check: while (j < p.nAction) : (j += 1) {
                        if (act_items[j].lookahead == cast(i32, j) + p.mnLookahead - i) break :j_check;
                    }
                    if (j == p.nAction) {
                        break :i_loop; // Fits in empty slots
                    }
                }
            }
        }
        // Insert transaction set at index i.
        if (p_check1) {
            dprint("Acttab:", .{});
            for (0..p.nLookahead) |j| {
                dprint(" {d}", .{look_items[j].lookahead});
            }
            dprint(" inserted at {d}\n", .{i});
        }
        for (0..p.nLookahead) |j| {
            const k = look_items[j].lookahead - p.mnLookahead + i;
            act_items[uint(k)] = look_items[j];
            if (k >= p.nAction) p.nAction = @intCast(k + 1);
        }
        if (makeItSafe and i + p.nterminal >= p.nAction) p.nAction = @intCast(i + p.nterminal + 1);
        p.nLookahead = 0;

        // Return the offset that is added to the lookahead in order to get the
        // index into yy_action of the action
        return @intCast(i - p.mnLookahead);
    }

    // [792]
    /// Return the size of the action table without the trailing syntax error entries.
    pub fn actionSize(acttab: *const ActTable) u32 {
        var n = acttab.nAction;
        while (n > 0 and acttab.aAction[n - 1].lookahead < 0) : (n -= 1) {}
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
fn FindRulePrecedences(zyt: *Zitron) void {
    // TODO: yacc uses the rightmost symbol apparently.  Do we want
    // that to be an option?  I think the precedence disambiguator is
    // enough..
    var maybe_rp: ?*Rule = zyt.rule;
    while (maybe_rp) |rp| : (maybe_rp = rp.next) {
        if (rp.precsym == null) {
            var i: usize = 0;
            precsym: while (i < rp.rhs.len) : (i += 1) {
                const sp: *Symbol = rp.rhs[i];
                if (sp.type == .multiterminal) {
                    for (sp.subsym) |subsym| {
                        if (subsym.prec) |_| {
                            rp.precsym = subsym;
                            break :precsym;
                        }
                    }
                } else if (sp.prec) |_| {
                    rp.precsym = rp.rhs[i];
                    break :precsym;
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
fn FindFirstSets(zyt: *Zitron) !void {
    for (zyt.symbols) |sym| {
        dbgassert(sym.lambda == false);
    }
    for (zyt.nterminal..zyt.nsymbol) |i| {
        const sym = zyt.symbols[i];
        dbgassert(sym.type == .nonterminal);
        sym.firstset = try zyt.allocator.alloc(bool, set_size);
    }
    // First compute all lambdas
    var progress: bool = true;
    while (progress) {
        progress = false;
        var rp: ?*Rule = zyt.rule;
        walk: while (rp) |rule| : (rp = rule.next) {
            if (rule.lhs.lambda) continue :walk;
            var i: usize = 0;
            sym: while (i < rule.rhs.len) : (i += 1) {
                const sp = rule.rhs[i];
                dbgassert(sp.type == .nonterminal or sp.lambda == false);
                if (sp.lambda == false) break :sym;
            } // A rule with no nrhs, or, all lambda, is lambda.
            if (i == rule.rhs.len) {
                rule.lhs.lambda = true;
                progress = true;
            }
        }
    }

    // Now compute all first sets
    progress = true;
    while (progress) {
        progress = false;
        var rp: ?*Rule = zyt.rule;
        while (rp) |rule| : (rp = rule.next) {
            const s1 = rule.lhs;
            rhs: for (rule.rhs) |s2| {
                if (s2.type == .terminal) {
                    const p = SetAdd(s1.firstset, s2.index);
                    progress = progress or p;
                    break :rhs;
                } else if (s2.type == .multiterminal) {
                    for (s2.subsym) |ss2| {
                        progress = SetAdd(s1.firstset, ss2.index) or progress;
                    }
                    break :rhs;
                } else if (s1 == s2) {
                    if (s1.lambda == false) break :rhs;
                } else {
                    progress = SetUnion(s1.firstset, s2.firstset) or progress;
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
fn FindStates(zyt: *Zitron) !void {
    const sp: *Symbol = sp: {
        if (zyt.start.len > 0) {
            const maybe_sp = Symbol_find(zyt.start);
            if (maybe_sp) |_| {
                break :sp zyt.startRule.lhs;
            } else {
                ErrorMsg(zyt.filename, 0, "" ++
                    "The specified start symbol \"{s}\" is not " ++
                    "in a nonterminal of the grammar.  \"{s}\" will be used as the start " ++
                    "symbol instead.", .{ zyt.start, zyt.startRule.lhs.name });
                zyt.errorcnt += 1;
                break :sp zyt.startRule.lhs;
            }
        } else {
            // OG checks if startRule pointer is defined, we (and it) ensure
            // that it is before we get here.
            break :sp zyt.startRule.lhs;
        }
    };
    // Make sure the start symbol doesn't occur on the right-hand side of
    // any rule.  Report an error if it does.  (YACC would generate a new
    // start symbol in this case.)
    var rp: ?*Rule = zyt.rule;
    while (rp) |rule| : (rp = rule.next) {
        for (rule.rhs) |rhs| {
            if (rhs == sp) {
                ErrorMsg(zyt.filename, rule.line, "" ++
                    "The start symbol \"{s}\" occurs on the " ++
                    "right-hand side of a rule. This will result in a parser which " ++
                    "does not work properly.", .{sp.name});
                zyt.errorcnt += 1;
            }
            //| NOTE: the previous comparison says FIX ME:  Deal with
            //| multiterminals.  I think this is the fix, it's not actually
            //| clear this condition can be triggered in any case.
            if (rhs.type == .multiterminal) {
                // Token class: could have the same name.
                if (mem.eql(u8, rhs.name, sp.name)) {
                    ErrorMsg(zyt.filename, 0, "" ++
                        "The start symbol has a synonym declared as a token class. This will " ++
                        "result in a parser which does not work properly.", .{});
                    zyt.errorcnt += 1;
                }
                for (rhs.subsym) |subsym| {
                    if (subsym == sp) {
                        ErrorMsg(zyt.filename, 0, "" ++
                            "The start symbol {s} appears as a terminal in a multiterminal. " ++
                            "This was thought to be impossible.", .{sp.name});
                        zyt.errorcnt += 1;
                    }
                }
            }
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
    _ = try getstate(zyt);
}

/// Used only in reporting via p_check1
threadlocal var state_count: usize = 0;

// [967]
// Return a pointer to a state which is described by the configuration
// list which has been built from calls to Configlist_add.
fn getstate(zyt: *Zitron) Allocator.Error!*State {
    // Extract the sorted basis of the new state.  The basis was constructed
    // by prior calls to "Configlist_addbasis()".
    Configlist_sortbasis();
    const bp = Configlist_basis();
    if (p_check1) {
        state_count += 1;
        dprint("State basis {d}: ", .{state_count});
        var m_bp: ?*Config = bp;
        while (m_bp) |a_bp| : (m_bp = a_bp.bp) {
            if (a_bp.dot < a_bp.rp.rhs.len) {
                dprint("{s}:{d} #({d}) {s} ", .{ a_bp.rp.lhs.name, a_bp.rp.iRule, a_bp.dot, a_bp.rp.rhs[a_bp.dot].name });
            } else {
                dprint("{s}:{d} #({d}) [end] ", .{ a_bp.rp.lhs.name, a_bp.rp.iRule, a_bp.dot });
            }
        }
        dprint("\n", .{});
    }
    const maybe_stp = State_find(bp);
    if (maybe_stp) |stp| {
        if (p_check1) {
            dprint("  state found: {d}\n", .{stp.statenum});
        }
        // A state with the same basis already exists!  Copy all the follow-set
        // propagation links from the state under construction into the
        // preexisting state, then return a pointer to the preexisting state
        var maybe_x: ?*Config = bp;
        var maybe_y: ?*Config = stp.bp;
        while (maybe_x != null and maybe_y != null) {
            const x = maybe_x.?;
            const y = maybe_y.?;
            Plink_copy(&y.bplp, x.bplp);
            Plink_delete(x.fplp);
            x.fplp = null;
            x.bplp = null;
            maybe_x = x.bp;
            maybe_y = y.bp;
        }
        Configlist_eat(Configlist_return(), zyt.allocator);
        return stp;
    } else {
        // This really is a new state.  Construct all the details
        if (p_check1) {
            dprint("  state not found\n", .{});
        }
        try Configlist_closure(zyt); //  Compute the configuration closure */
        Configlist_sort(); //  Sort the configuration closure */
        const cfp = Configlist_return().?; //  Get a pointer to the config list */
        if (p_check1) {
            dprint("cfp: ", .{});
            var cfp_count: usize = 0;
            var mcfp: ?*Config = cfp;
            while (mcfp) |a_cfp| : (mcfp = a_cfp.next) {
                cfp_count += 1;
                dprint("*", .{});
            }
            dprint(" ({d})\n", .{cfp_count});
        }
        const stp = try State_new(); //  A new state structure */
        stp.bp = bp;
        stp.cfp = cfp;
        stp.statenum = zyt.nstate;
        zyt.nstate += 1;
        stp.ap = null;
        dbgassert(try State_insert(stp, bp));
        try buildshifts(zyt, stp);
        return stp;
    }
}

///
/// Return true if two symbols are the same.  Normally this is
/// a matter of pointer comparison, multiterminals are the
/// exception.
fn same_symbol(a: *const Symbol, b: *const Symbol) bool {
    if (a == b) return true;
    if (a.type != .multiterminal) return false;
    if (b.type != .multiterminal) return false;
    if (a.subsym.len != b.subsym.len) return false;
    for (a.subsym, b.subsym) |asub, bsub| {
        if (asub != bsub) return false;
    }
    return true;
}

fn buildshifts(zyt: *Zitron, stp: *State) !void {
    var maybe_cfp: ?*Config = stp.cfp; // For looping thru the config closure of "stp"
    // Initialize with a conveniently available symbol, this is never used:
    // (So we don't do it)
    // /* Each configuration becomes complete after it contributes to a successor
    // ** state.  Initially, all configurations are incomplete.
    if (p_check_next) {
        dprint("buildshifts entry on stp {d}\n", .{stp.statenum});
    }
    while (maybe_cfp) |cfp| : (maybe_cfp = cfp.next) {
        if (p_check_next) dprint("Reset cfg {d}-{d}\n", .{ cfp.rp.iRule, cfp.dot });
        cfp.status = .incomplete;
    }
    maybe_cfp = stp.cfp;
    // Loop through all configurations of the state "stp".
    while (maybe_cfp) |cfp| : (maybe_cfp = cfp.next) {
        if (p_debug) dprint("outer config {s}: {s} dot ({d}) nrhs {d} len {d} ", .{
            cfp.rp.lhs.name,
            @tagName(cfp.status),
            cfp.dot,
            cfp.rp.nrhs,
            cfp.rp.rhs.len,
        });
        if (cfp.status == .complete) continue; // Already used by inner loop
        if (cfp.dot >= cfp.rp.rhs.len) continue; // Can't shift this config
        Configlist_reset(); // Reset the new config set
        const sp = cfp.rp.rhs[cfp.dot]; // Symbol following the dot in configuration "cfp"
        var maybe_bcfp: ?*Config = cfp; // For the inner loop on config closure of "stp"
        while (maybe_bcfp) |bcfp| : (maybe_bcfp = bcfp.next) {
            if (bcfp.status == .complete) continue; // Already used
            if (bcfp.dot >= bcfp.rp.rhs.len) continue; // Can't shift this one
            const bsp = bcfp.rp.rhs[bcfp.dot]; //  Get symbol after dot
            if (!same_symbol(bsp, sp)) continue; //  Must be same as for "cfp"
            bcfp.status = .complete; //  Mark this config as used
            if (p_check_next) {
                dprint("  basis from {s}: {d} -> {d}\n", .{
                    bcfp.rp.lhs.name,
                    bcfp.dot,
                    bcfp.dot + 1,
                });
            }
            const newcfg = try Configlist_addbasis(bcfp.rp, bcfp.dot + 1);
            try Plink_add(&newcfg.bplp, bcfp);
        }
        // /* Get a pointer to the state described by the basis configuration set
        // ** constructed in the preceding loop */
        const newstp = try getstate(zyt);
        // /* The state "newstp" is reached from the state "stp" by a shift action
        // ** on the symbol "sp" */
        if (sp.type == .multiterminal) {
            if (p_check2) {
                dprint("buildshifts: adding state {s}\n", .{sp.name});
            }
            for (sp.subsym) |subsym| {
                try Action.addState(&stp.ap, .shift, subsym, newstp);
            }
        } else {
            try Action.addState(&stp.ap, .shift, sp, newstp);
        }
    }
}

//| [1077]

///
/// Construct the propagation links
///
fn FindLinks(zyt: *Zitron) !void {
    // Housekeeping detail:
    // Add to every propagate link a pointer back to the state to
    // which the link is attached.
    for (zyt.sorted) |stp| {
        var maybe_cfp: ?*Config = stp.cfp;
        while (maybe_cfp) |cfp| : (maybe_cfp = cfp.next) {
            if (p_check1) {
                dprint("cfp: {s}:{d} -> {d}\n", .{ cfp.rp.lhs.name, cfp.rp.index, stp.statenum });
            }
            cfp.stp = stp;
        }
    }
    // Convert all backlinks into forward links.  Only the forward
    // links are used in the follow-set computation.
    for (zyt.sorted) |stp| {
        var maybe_cfp: ?*Config = stp.cfp;
        while (maybe_cfp) |cfp| : (maybe_cfp = cfp.next) {
            if (p_check1) {
                dprint("cfp: {s}:{d} <-> ", .{ cfp.rp.lhs.name, cfp.rp.index });
            }
            var maybe_plp: ?*PLink = cfp.bplp;
            while (maybe_plp) |plp| : (maybe_plp = plp.next) {
                var other = plp.cfp;
                if (p_check1) {
                    dprint("{s}:{d} ({d}), ", .{ other.rp.lhs.name, other.rp.index, other.dot });
                }
                try Plink_add(&other.fplp, cfp);
            }
            if (p_check1) dprint("\n", .{});
        }
    }
}

// [1112]
/// Compute all followsets.
///
/// A followset is the set of all symbols which can come immediately
/// after a configuration.
fn FindFollowSets(zyt: *Zitron) void {
    for (zyt.sorted) |stp| {
        var maybe_cfp: ?*Config = stp.cfp;
        while (maybe_cfp) |cfp| : (maybe_cfp = cfp.next) {
            cfp.status = .incomplete;
        }
    }
    var c_count: usize = 0;
    var progress = true;
    while (progress) {
        progress = false;
        for (zyt.sorted) |stp| {
            var maybe_cfp: ?*Config = stp.cfp;
            states: while (maybe_cfp) |cfp| : (maybe_cfp = cfp.next) {
                if (cfp.status == .complete) continue :states;
                var maybe_plp: ?*PLink = cfp.fplp;
                while (maybe_plp) |plp| : (maybe_plp = plp.next) {
                    const changed = SetUnion(plp.cfp.fws, cfp.fws);
                    if (p_check1) {
                        c_count += 1;
                        dprint(
                            "#{d} follow set: {s}:{d} ",
                            .{ c_count, plp.cfp.rp.lhs.name, plp.cfp.rp.index },
                        );
                        if (changed) {
                            dprint("change\n", .{});
                        } else {
                            dprint("no change\n", .{});
                        }
                    }
                    if (changed) {
                        plp.cfp.status = .incomplete;
                        progress = true;
                    }
                }
                cfp.status = .complete;
            }
        }
    }
}

// Compute the reduce actions, and resolve conflicts.
//
fn FindActions(zyt: *Zitron) !void {
    // Add all of the reduce actions
    // A reduce action is added for each element of the followset of
    // a configuration which has its dot at the extreme right.
    //
    for (zyt.sorted) |stp| { // Loop over all states
        var maybe_cfp: ?*Config = stp.cfp;
        while (maybe_cfp) |cfp| : (maybe_cfp = cfp.next) { // Loop over all configurations
            if (cfp.rp.rhs.len == cfp.dot) { // Is dot at extreme right?
                for (0..zyt.nterminal) |j| {
                    if (cfp.fws[j]) {
                        //  Add a reduce action to the state "stp" which will reduce by the
                        //  rule "cfp->rp" if the lookahead symbol is "lemp->symbols[j]"
                        try Action.addRule(&stp.ap, .reduce, zyt.symbols[j], cfp.rp);
                    }
                }
            }
        }
    }
    //  Add the accepting token
    const sp: *Symbol = sym: {
        if (zyt.start.len > 0) {
            const sp_start = Symbol_find(zyt.start);
            if (sp_start) |sps| {
                break :sym sps;
            } else {
                break :sym zyt.startRule.lhs;
            }
        } else break :sym zyt.startRule.lhs;
    };
    // Add to the first state (which is always the starting state of the
    // finite state machine) an action to ACCEPT if the lookahead is the
    // start nonterminal.
    try Action.addRule(&zyt.sorted[0].ap, .accept, sp, null);
    //   Resolve conflicts
    for (zyt.sorted) |stp| {
        stp.ap = if (stp.ap) |ap| Action.sort(ap) else null;
        var m_ap: ?*Action = stp.ap;
        while (m_ap) |ap| : (m_ap = ap.next) {
            var nap = ap.next;
            while (nap != null and nap.?.sp == ap.sp) : (nap = nap.?.next) {
                // The two actions "ap" and "nap" have the same lookahead.
                // Figure out which one should be used */
                if (p_check1) {
                    dprint("find state: before .{s} .{s}\n", .{ @tagName(ap.type), @tagName(nap.?.type) });
                }
                zyt.nconflict += resolve_conflict(ap, nap.?);
                if (p_check1) {
                    dprint("find state: after .{s} .{s}\n", .{ @tagName(ap.type), @tagName(nap.?.type) });
                }
            }
        }
    }
    // Report an error for each rule that can never be reduced.
    var m_rp: ?*Rule = zyt.rule;
    while (m_rp) |rp| : (m_rp = rp.next) rp.canReduce = false;
    for (zyt.sorted) |stp| {
        var m_ap = stp.ap;
        while (m_ap) |ap| : (m_ap = ap.next) {
            if (ap.type == .reduce) ap.x.rp.?.canReduce = true;
        }
    }
    m_rp = zyt.rule;
    while (m_rp) |rp| : (m_rp = rp.next) {
        if (rp.canReduce) continue;
        ErrorMsg(zyt.filename, rp.ruleline, "" ++
            "This rule can not be reduced.\n", .{});
        zyt.errorcnt += 1;
    }
}

fn resolve_conflict(apx: *Action, apy: *Action) u32 {
    dbgassert(apx.sp == apy.sp); // Otherwise there would be no conflict
    var errcnt: u32 = 0;
    // TODO: This is the major overhaul to use a tagged union.
    if (apx.type == .shift and apy.type == .shift) {
        apy.type = .ssconflict;
        errcnt += 1;
    }
    if (apx.type == .shift and apy.type == .reduce) {
        const spx = apx.sp;
        const maybe_spy = apy.x.rp.?.precsym;
        if (maybe_spy == null) {
            // Not enough precedence information
            apy.type = .srconflict;
            errcnt += 1; // And we can bail early
            return errcnt;
        } // So we can do this:
        const spy = maybe_spy.?;
        if (spx.prec == null or spy.prec == null) {
            // Not enough precedence information.
            apy.type = .srconflict;
            errcnt += 1;
        } else if (spx.prec.? > spy.prec.?) { // higher precedence wins
            apy.type = .rd_resolved;
        } else if (spx.prec.? < spy.prec.?) {
            apx.type = .sh_resolved;
        } else if (spx.prec.? == spy.prec.?) { // Use operator associativity to break tie
            if (spx.assoc == .right) {
                apy.type = .rd_resolved;
            } else if (spx.assoc == .left) {
                apx.type = .sh_resolved;
            } else {
                dbgassert(spx.assoc == .none);
                apx.type = .@"error";
                // NOTE: this means the /parse/ is in error,
                // not the /grammar/, eg a == b == c in C.
            }
            // TODO: Bison has a compile error version of this kind of
            // precendence, we could add that, would it be of any use?
        }
    } else if (apx.type == .reduce and apy.type == .reduce) {
        const maybe_spx = apx.x.rp.?.precsym;
        const maybe_spy = apy.x.rp.?.precsym;
        if (maybe_spx == null or maybe_spy == null or maybe_spx.?.prec == null or
            maybe_spy.?.prec == null or maybe_spx.?.prec.? == maybe_spy.?.prec.?)
        {
            apy.type = .rrconflict;
            errcnt += 1;
            return errcnt;
        }
        // TODO: decide whether we resolve reduces on precedence, or make
        // that optional, or what.  It's fairly opinionated behavior.
        const spx = maybe_spx.?;
        const spy = maybe_spy.?;
        if (spy.prec.? < spx.prec.?) {
            apy.type = .rd_resolved;
        } else if (spx.prec.? < spy.prec.?) {
            apx.type = .rd_resolved;
        } // Equality is checked in the first if statement.
    } else {
        // The REDUCE/SHIFT case cannot happen because SHIFTs come before
        // REDUCEs on the list.  If we reach this point it must be because
        // the parser conflict had already been resolved.
        // zig fmt: off
        dbgassert(
            apx.type == .sh_resolved or
            apx.type == .rd_resolved or
            apx.type == .ssconflict or
            apx.type == .srconflict or
            apx.type == .rrconflict or

            apy.type == .sh_resolved or
            apy.type == .rd_resolved or
            apy.type == .ssconflict or
            apy.type == .srconflict or
            apy.type == .rrconflict
        );
        // zig fmt: on
    }
    return errcnt;
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
    waiting_for_arrow_or_rhs,
    in_rhs,
    impl_1,
    impl_lhs1,
    impl_lhs2,
    impl_rhs1,
    impl_rhs2,
    waiting_for_impl_directive,
    lhs_alias_1,
    lhs_alias_2,
    lhs_alias_3,
    rhs_alias_1,
    rhs_alias_2,
    precedence_mark_1,
    precedence_mark_2,
    resync_after_rule_error,
    resync_after_decl_error,
    resync_after_impl_error,
    waiting_for_destructor_symbol,
    waiting_for_datatype_symbol,
    waiting_for_fallback_id,
    waiting_for_wildcard_id,
    waiting_for_class_id,
    waiting_for_class_token,
    waiting_for_token_name,
};

pub const ParserState = struct {
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
    gp: *Zitron,
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
    nrhs: usize,
    /// RHS symbols
    rhs: []*Symbol,
    /// Aliases for each RHS symbol (or null)
    alias: [][]const u8, // We'll use empty slices as per usual
    /// Previous rule parsed
    prevrule: ?*Rule,
    /// Is the previous rule a ditto?
    dittoed: bool,
    /// Impl, if we're working on one
    impl: ?*Impl,
    /// Impl rhsalias index
    impl_idx: u8,
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

    pub const empty: ParserState = .{
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
        .dittoed = false,
        .impl = null,
        .impl_idx = 0,
        .declkeyword = "",
        .declargslot = null,
        .insertLineMacro = false,
        .decllinenoslot = null,
        .declassoc = .unk,
        .preccounter = 0,
        .firstrule = null,
        .lastrule = null,
    };

    pub fn create(allocator: Allocator, gp: *Zitron) !*ParserState {
        var psp = try allocator.create(ParserState);
        errdefer allocator.destroy(psp);
        try psp.setup(gp);
        return psp;
    }

    pub fn setup(psp: *ParserState, gp: *Zitron) !void {
        psp.* = .empty;
        psp.allocator = gp.allocator;
        psp.gp = gp;
        psp.rhs = try gp.allocator.alloc(*Symbol, MAXRHS);
        errdefer gp.allocator.free(psp.rhs);
        psp.alias = try gp.allocator.alloc([]const u8, MAXRHS);
        errdefer gp.allocator.free(psp.alias);
    }

    pub fn deinit(ps: *ParserState) void {
        ps.allocator.free(ps.rhs);
        ps.allocator.free(ps.alias);
    }

    pub fn destroy(ps: *ParserState) void {
        ps.deinit();
        ps.allocator.destroy(ps);
    }
};

const PpState = enum {
    ok,
    pp_syntax_error,
};

/// The text in the input is part of the argument to an %ifdef or %ifndef.
/// Evaluate the text as a boolean expression.  Return true or false.
/// Actually (zig edition): returns one or zero, because the consumer uses the
/// result variable to track nested ifdefs.
fn eval_preprocessor_boolean(opt: *Options, errcnt: *usize, z: []const u8, lineno: usize) u8 {
    var dummy: usize = 0;
    return if (eval_impl(opt, errcnt, z, lineno, &dummy) catch unreachable) 1 else 0;
}

// TODO: Re-evaluate all of this once have a reproducing case for the
// error message.

/// `progress` is some wacky thing, we're imitating the all-powerful
/// C integer. If 0 we're not in a recursive call, if positive, we
/// are.
fn eval_impl(opt: *Options, errcnt: *usize, z: []const u8, lineno: usize, progress: *usize) !bool {
    var neg: bool = false; // Term is negated
    var res: bool = false; // Result
    var okTerm: bool = true; // Ok to have a term
    var i: usize = 0;
    const which: PpState = .ok;
    goto: switch (which) {
        .ok => {
            scan: while (i < z.len) : (i += 1) {
                const fwd = i + 1 < z.len;
                const c = z[i];
                if (isSpace(c)) continue :scan;
                if (c == '!') {
                    if (!okTerm) continue :goto .pp_syntax_error;
                    neg = !neg;
                    continue :scan;
                }
                if (c == '|' and fwd and z[i + 1] == '|') {
                    if (okTerm) continue :goto .pp_syntax_error;
                    if (res) return true;
                    i += 1;
                    okTerm = true;
                    continue :scan;
                }
                if (c == '&' and fwd and z[i + 1] == '&') {
                    if (okTerm) continue :goto .pp_syntax_error;
                    if (!res) return false;
                    i += 1;
                    okTerm = true;
                    continue :scan;
                }
                if (c == '(') {
                    if (!okTerm) continue :goto .pp_syntax_error;
                    var k = i + 1;
                    var n: usize = 1;
                    while (k < z.len) : (k += 1) {
                        if (z[k] == ')') {
                            n -= 1;
                            if (n == 0) {
                                var prog: usize = i;
                                res = eval_impl(opt, errcnt, z[i..k], lineno, &prog) catch {
                                    i = prog;
                                    continue :goto .pp_syntax_error;
                                };
                                i = k;
                                if (neg) {
                                    res = !res;
                                    neg = false;
                                }
                                continue :scan;
                            }
                        } else if (z[i] == '(') {
                            n += 1;
                        }
                    } else continue :goto .pp_syntax_error;
                }
                if (isAlpha(c)) {
                    var k = i + 1;
                    while (k < z.len and (isAlnum(z[k]) or z[k] == '_')) : (k += 1) {}
                    res = false;
                    {
                        var j: usize = 0;
                        check_defs: while (j < opt.azDefine.len) : (j += 1) {
                            if (strcmp(
                                z[i..k],
                                opt.azDefine[j],
                            )) {
                                if (!opt.bDefineUsed[j]) {
                                    opt.bDefineUsed[j] = true;
                                    opt.nDefineUsed += 1;
                                }
                                res = true;
                                break :check_defs;
                            }
                        }
                    }
                    i = k - 1;
                    if (neg) {
                        res = !res;
                        neg = false;
                    }
                    okTerm = false;
                    continue :scan;
                }
                continue :goto .pp_syntax_error;
            }
        },
        .pp_syntax_error => {
            if (progress.* == 0) {
                dprint("%if syntax error on line {d}.\n", .{lineno});
                // We already sliced z down to one line, so this is fine
                dprint("  {s} <-- syntax error here\n", .{z[i..]});
                errcnt.* += 1;
            } else {
                progress.* += i;
                return error.ScrollUp52LinesToContinue;
            }
        },
    }
    return res;
}

/// Run the preprocessor over the input file text.  The global variables
/// azDefine[0] through azDefine[nDefine-1] contains the names of all defined
/// macros.  This routine looks for "%ifdef" and "%ifndef" and "%endif" and
/// comments them out.  Text in between is also commented out as appropriate.
fn preprocess_input(opt: *Options, errcnt: *usize, z: [:0]u8) void {
    var exclude: isize = 0; // Handles nested %ifdefs so not boolean
    var start: usize = 0;
    var lineno: usize = 1;
    var start_lineno: usize = 1;
    var i = start;
    var j = start;
    const zl = z.len;
    var level: isize = 0;
    var level_lineno: usize = 1;
    scan: while (z[i] != 0) : (i += 1) {
        if (z[i] == '\n') lineno += 1;
        if (z[i] != '%' or (i > 0 and z[i - 1] != '\n')) continue :scan;
        if (i + 6 <= zl and strcmp(z[i..][0..6], "%endif") and isSpace(z[i + 6])) {
            level -= 1;
            if (level < 0) {
                dprint("unmatched %endif on line {d}\n", .{lineno});
                errcnt.* += 1;
            }
            if (exclude != 0) {
                exclude -= 1;
                if (exclude == 0) {
                    j = start;
                    while (j < i) : (j += 1) {
                        if (z[j] != '\n') z[j] = ' ';
                    }
                }
            }
            j = i;
            while (z[j] != 0 and z[j] != '\n') : (j += 1) z[j] = ' ';
        } else if (i + 5 < zl and strcmp(z[i..][0..5], "%else") and isSpace(z[i + 5])) {
            if (exclude == 1) {
                exclude = 0;
                j = start;
                while (j < i) : (j += 1) {
                    if (z[j] != '\n') z[j] = ' ';
                }
            } else if (exclude == 0) {
                exclude = 1;
                start = i;
                start_lineno = lineno;
            }
            j = i;
            while (z[j] != 0 and z[j] != '\n') : (j += 1) z[j] = ' ';
        } else if (i + 8 <= zl and
            (strcmp(z[i..][0..7], "%ifdef ") or
                strcmp(z[i..][0..4], "%if ") or
                strcmp(z[i..][0..8], "%ifndef ")))
        {
            level += 1;
            level_lineno = lineno;
            if (exclude != 0) {
                exclude += 1;
            } else {
                j = i;
                while (z[j] != ' ') : (j += 1) {}
                const iBool = j;
                const isNot = j == i + 7;
                while (z[j] != 0 and z[j] != '\n') : (j += 1) {}
                if (p_check1) dprint("preprocessor evaluates '{s}' ", .{z[iBool..j]});
                exclude = eval_preprocessor_boolean(opt, errcnt, z[iBool..j], lineno);
                if (p_check1) dprint("as {} ", .{exclude == 1});
                if (!isNot) exclude = if (exclude != 0) 0 else 1;
                if (p_check1) dprint("then {}\n", .{exclude == 1});
                if (exclude == 1) {
                    start = i;
                    start_lineno = lineno;
                }
            }
            j = i;
            while (z[j] != 0 and z[j] != '\n') : (j += 1) z[j] = ' ';
        }
    }
    if (exclude != 0) {
        dprint("unterminated %ifdef starting on line {d}\n", .{start_lineno});
        errcnt.* += 1;
    } else if (level > 0) {
        if (level == 1) {
            dprint("missing %endif starting on line {d}\n", .{level_lineno});
        } else {
            dprint("missing {d} %endifs, last starts on line {d}\n", .{ level, level_lineno });
        }
        errcnt.* += 1;
    }
}

/// In spite of its name, this function is really a scanner.  It reads
/// in the entire input file (all at once) then tokenizes it.  Each
/// token is passed to the function "parseonetoken" which builds all
/// the appropriate data structures in the global state vector "gp".
fn Parse(psp: *ParserState) !void {
    // TODO: the original creates PState (and Lemon) on the stack,
    // and does the former here, passing in the latter.  Cleanup should
    // do likewise.
    const filebuf = if (psp.gp.opt.fifo) filebuf: {
        var stdin_buffer: [4096]u8 = undefined;
        var stdin_reader = std.Io.File.stdin().readerStreaming(psp.gp.io, &stdin_buffer);
        break :filebuf stdin_reader.interface.allocRemainingAlignedSentinel(
            psp.allocator,
            .unlimited,
            .of(u8),
            0,
        ) catch |err| switch (err) {
            error.ReadFailed => return stdin_reader.err.?,
            else => |e| return e,
        };
    } else filebuf: {
        const file = if (std.Io.Dir.cwd().openFile(psp.gp.io, psp.filename, .{})) |f| file: {
            break :file f;
        } else |err| {
            // TODO: nicer message here
            std.debug.print("File open error {s}", .{@errorName(err)});
            exit(@max(1, @as(u8, @truncate(@intFromError(err)))));
        };
        defer file.close(psp.gp.io);
        const end_pos = (try file.stat(psp.gp.io)).size;
        const filebuf = try psp.allocator.allocSentinel(u8, end_pos, 0);
        const read_bytes = try file.readPositionalAll(psp.gp.io, filebuf, 0);
        if (read_bytes < end_pos) {
            std.debug.print("didnt read to end of file {s}\n", .{psp.filename});
            std.process.exit(1);
        }
        break :filebuf filebuf;
    };
    defer psp.allocator.free(filebuf);
    // /* Make an initial pass through the file to handle %ifdef and %ifndef */
    preprocess_input(&psp.gp.opt, &psp.gp.errorcnt, filebuf);
    if (psp.gp.errorcnt > 0 and !psp.gp.opt.fifo) return;
    if (psp.gp.printPreprocessed) {
        var stdout_buffer: [1024]u8 = undefined;
        var stdout_writer = std.Io.File.stdout().writer(psp.gp.io, &stdout_buffer);
        const stdout = &stdout_writer.interface;
        try stdout.print("{s}\n", .{filebuf});
        try stdout.flush();
        return;
    }

    try scan(psp, filebuf);
    if (psp.gp.nrule > 0) {
        psp.gp.rule = psp.firstrule.?;
    }
    psp.gp.errorcnt = psp.errorcnt;
}

fn parseonetoken(psp: *ParserState, x_init: []const u8) !void {
    const x = try Strsafe(x_init);
    // This seems to be presumed (?)
    assert(x.len != 0);
    if (p_print) std.debug.print("state: {s}  ", .{@tagName(psp.state)});
    if (p_check1) if (x.len < 50) {
        std.debug.print("token: {s}\n", .{x});
    } else {
        std.debug.print("token: {s}...\n", .{x[0..50]});
    };
    if (p_errcnt) if (psp.gp.errorcnt > 0) {
        std.debug.print("error count: {d}\n", .{psp.gp.errorcnt});
    };
    state: switch (psp.state) {
        .initialize => {
            psp.prevrule = null;
            psp.preccounter = 0;
            psp.firstrule, psp.lastrule = .{ null, null };
            psp.gp.nrule = 0;
            continue :state .waiting_for_decl_or_rule;
        },
        .waiting_for_decl_or_rule => {
            if (x[0] == '%') {
                psp.state = .waiting_for_decl_keyword;
                psp.prevrule = null;
                psp.impl = null;
                psp.impl_idx = 0;
                psp.dittoed = false;
            } else if (isLower(x[0])) {
                psp.lhs = try Symbol_new(x);
                psp.nrhs = 0;
                psp.impl = null;
                psp.impl_idx = 0;
                psp.lhsalias = "";
                psp.state = .waiting_for_arrow;
                psp.dittoed = false;
            } else if (x[0] == '`') {
                if (x.len >= 2 and x[1] == '`') {
                    if (psp.prevrule) |prev| {
                        psp.lhs = prev.lhs;
                        psp.lhsalias = prev.lhsalias;
                        psp.impl = null;
                        psp.impl_idx = 0;
                        psp.nrhs = 0;
                        psp.dittoed = true;
                        psp.state = .waiting_for_arrow_or_rhs;
                    } else {
                        ErrorMsg(psp.filename, psp.tokenlineno, "" ++
                            "There is no prior rule, the ditto is invalid here.", .{});
                        psp.errorcnt += 1;
                        psp.state = .resync_after_rule_error;
                    }
                } else {
                    ErrorMsg(psp.filename, psp.tokenlineno, "" ++
                        "Unexpected {s} token, did you mean \"``\"?", .{x});
                    psp.errorcnt += 1;
                    psp.state = .resync_after_rule_error;
                }
            } else if (x[0] == '{') {
                if (psp.impl) |_| {
                    ErrorMsg(psp.filename, psp.tokenlineno, "" ++
                        "The rule already has an impl name, cannot attach a code block", .{});
                    psp.errorcnt += 1;
                } else if (psp.prevrule) |prev| {
                    if (prev.code.len != 0) {
                        ErrorMsg(psp.filename, psp.tokenlineno, "" ++
                            "Code fragment beginning on this line is not the first " ++
                            "to follow the previous rule.", .{});
                        psp.errorcnt += 1;
                        psp.state = .resync_after_rule_error;
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
                    psp.state = .resync_after_rule_error;
                }
            } else if (x[0] == '[') {
                psp.state = .precedence_mark_1;
            } else if (x[0] == '@') {
                if (psp.impl) |imp| {
                    ErrorMsg(psp.filename, psp.tokenlineno, "" ++
                        "This rule already has an impl name {s}, saw {s}", .{ imp.name, x });
                    psp.errorcnt += 1;
                    psp.state = .resync_after_impl_error;
                } else {
                    const impl = try impl_safe.get(x);
                    psp.impl = impl;
                    psp.impl_idx = 0;
                    if (impl.rule) |rp| {
                        ErrorMsg(psp.filename, psp.tokenlineno, "" ++
                            "This impl name {s} already has a rule {s}, they must be unique", .{ x, rp.lhs.name });
                        psp.errorcnt += 1;
                        psp.state = .resync_after_impl_error;
                    } else {
                        if (psp.prevrule) |prev| {
                            impl.rule = prev;

                            if (try validateAndRepairImpl(psp, impl, prev)) {
                                if (impl.line == 0) {
                                    dbgassert(impl.rhsalias.len == 0);
                                    impl.rhsalias = try psp.allocator.realloc(impl.rhsalias, prev.rhsalias.len);
                                    @memset(impl.rhsalias, "");
                                }
                                psp.state = .impl_1;
                            } else {
                                psp.state = .resync_after_impl_error;
                            }
                        } else {
                            ErrorMsg(psp.filename, psp.tokenlineno, "" ++
                                "No previous rule to attach an impl name to", .{});
                            psp.errorcnt += 1;
                            psp.state = .resync_after_impl_error;
                        }
                    }
                }
            } else {
                ErrorMsg(psp.filename, psp.tokenlineno, "" ++
                    "Token {s} should be either \"%\"{s}.", //
                    .{ x, if (psp.prevrule) |_| ", a nonterminal name, or a code block" else " or a nonterminal name" });
                psp.state = .resync_after_impl_error;
                psp.errorcnt += 1;
            }
        },
        .precedence_mark_1 => {
            if (!isUpper(x[0])) {
                ErrorMsg(psp.filename, psp.tokenlineno, "" ++
                    "The precedence symbol must be a terminal, not '{s}'.", .{x});
                psp.errorcnt += 1;
            } else if (psp.prevrule) |prev| {
                if (prev.precsym) |_| {
                    ErrorMsg(psp.filename, psp.tokenlineno, "" ++
                        "Precedence mark '[{s}]' on this line is not the first " ++
                        "to follow the previous rule.", .{x});
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
            if (x.len == 3 and x[0] == ':' and x[1] == ':' and x[2] == '=') {
                psp.state = .in_rhs;
            } else if (x[0] == '(') {
                psp.state = .lhs_alias_1;
            } else {
                if (psp.dittoed) {
                    ErrorMsg(psp.filename, psp.tokenlineno, "" ++
                        "Expected to see a \"::=\" following the \"``\".", .{});
                } else {
                    ErrorMsg(psp.filename, psp.tokenlineno, "" ++
                        "Expected to see a \"::=\" following the LHS symbol \"{s}\".", .{psp.lhs.name});
                }
                psp.errorcnt += 1;
                psp.state = .resync_after_rule_error;
            }
        },
        .waiting_for_arrow_or_rhs => {
            if (x[0] == ':') {
                continue :state .waiting_for_arrow;
            } else {
                continue :state .in_rhs;
            }
        },
        .impl_1 => {
            if (x[0] == '(') {
                psp.state = .impl_lhs1;
            } else {
                ErrorMsg(psp.filename, psp.tokenlineno, "" ++
                    "Impl \"{s}\" must name the rule aliases", .{psp.impl.?.name});
                psp.errorcnt += 1;
                psp.state = .resync_after_impl_error;
            }
        },
        .impl_lhs1 => {
            if (isAlpha(x[0])) {
                if (psp.impl) |impl| {
                    if (impl.lhsalias.len > 0 and !strcmp(impl.lhsalias, x)) {
                        ErrorMsg(psp.filename, psp.tokenlineno, "" ++
                            "Rule impl name \"{s}\" has alias \"{s}\" already, not \"{s}\"", .{
                            impl.name,
                            impl.lhsalias,
                            x,
                        });
                        psp.errorcnt += 1;
                        psp.state = .resync_after_impl_error;
                    } else if (impl.rule) |rule| {
                        if (!strcmp(rule.lhsalias, x)) {
                            ErrorMsg(psp.filename, psp.tokenlineno, "" ++
                                "Rules LHS alias is \"{s}\", not \"{s}\".", .{ rule.lhsalias, x });
                            psp.errorcnt += 1;
                            psp.state = .resync_after_impl_error;
                        } else {
                            impl.lhsalias = x;
                            psp.state = .impl_lhs2;
                        }
                    } else {
                        impl.lhsalias = x;
                        psp.state = .impl_lhs2;
                    }
                } else unreachable;
            } else if (x[0] == ';') {
                // no LHS alias (?)
                if (psp.impl.?.rule) |rule| {
                    if (rule.lhsalias.len > 0) {
                        ErrorMsg(psp.filename, psp.tokenlineno, "" ++
                            "Rule has LHS alias \"{s}\", rule impl name must match.", .{rule.lhsalias});
                        psp.errorcnt += 1;
                        psp.state = .resync_after_impl_error;
                    } else {
                        psp.state = .impl_rhs1;
                    }
                } else {
                    psp.state = .impl_rhs1;
                }
            } else if (x[0] == ')') {
                // no aliases at all
                if (psp.impl.?.rule) |rule| {
                    if (ruleHasAliases(rule)) {
                        ErrorMsg(psp.filename, psp.tokenlineno, "" ++
                            "Rule has aliases, rule impl name must as well", .{});
                        psp.errorcnt += 1;
                        psp.state = .resync_after_rule_error;
                    } else {
                        if (psp.prevrule == null) {
                            psp.state = .waiting_for_decl_arg;
                        } else {
                            psp.state = .waiting_for_decl_or_rule;
                        }
                    }
                } else {
                    if (psp.prevrule == null) {
                        psp.state = .waiting_for_decl_arg;
                    } else {
                        psp.state = .waiting_for_decl_or_rule;
                    }
                }
            } else {
                ErrorMsg(psp.filename, psp.tokenlineno, "" ++
                    "Expected a valid alias list in impl name, got {s}", .{x});
                psp.errorcnt += 1;
                psp.state = .resync_after_impl_error;
            }
        },
        .impl_lhs2 => {
            if (x[0] == ';') {
                psp.state = .impl_rhs1;
            } else if (x[0] == ')') {
                continue :state .impl_rhs2;
            } else {
                ErrorMsg(psp.filename, psp.tokenlineno, "" ++
                    "Impl LHS alias \"{s}\" must be followed by a semicolon", .{psp.impl.?.lhsalias});
                psp.errorcnt += 1;
                psp.state = .resync_after_impl_error;
            }
        },
        .impl_rhs1 => {
            if (isAlpha(x[0])) {
                const impl = psp.impl.?;
                if (psp.impl_idx >= impl.rhsalias.len) {
                    dbgassert(psp.impl_idx == impl.rhsalias.len);
                    impl.rhsalias = try psp.allocator.realloc(impl.rhsalias, impl.rhsalias.len + 1);
                    impl.rhsalias[psp.impl_idx] = "";
                }
                if (impl.rule) |rule| {
                    const rule_idx = nextNamedAliasIndex(rule.rhsalias, psp.impl_idx);
                    if (rule_idx == null) {
                        ErrorMsg(psp.filename, psp.tokenlineno, "" ++
                            "The rule impl name has more RHS aliases than the rule itself", .{});
                        psp.errorcnt += 1;
                        psp.state = .resync_after_impl_error;
                    } else if (!strcmp(rule.rhsalias[rule_idx.?], x)) {
                        ErrorMsg(psp.filename, psp.tokenlineno, "" ++
                            "Rule RHS alias \"{s}\" does not match rule impl's \"{s}\".", .{
                            rule.rhsalias[rule_idx.?], x,
                        });
                        psp.errorcnt += 1;
                        psp.state = .resync_after_impl_error;
                    } else {
                        psp.impl_idx = @intCast(rule_idx.?);
                        // Looking for the next rule can get us past what we've allocated
                        if (psp.impl_idx >= impl.rhsalias.len) {
                            const old_len = impl.rhsalias.len;
                            impl.rhsalias = try psp.allocator.realloc(impl.rhsalias, psp.impl_idx + 1);
                            @memset(impl.rhsalias[old_len..], "");
                        }
                        impl.rhsalias[psp.impl_idx] = x;
                        psp.state = .impl_rhs2;
                    }
                } else {
                    impl.rhsalias[psp.impl_idx] = x;
                    psp.state = .impl_rhs2;
                }
                psp.impl_idx += 1;
            } else if (x[0] == ')') {
                const impl = psp.impl.?;
                if (impl.rule) |rule| {
                    if (nextNamedAliasIndex(rule.rhsalias, psp.impl_idx)) |idx| {
                        ErrorMsg(psp.filename, psp.tokenlineno, "" ++
                            "Impl \"{s}\" missing RHS alias \"{s}\".", .{
                            impl.name, rule.rhsalias[idx],
                        });
                        psp.errorcnt += 1;
                        psp.state = .resync_after_impl_error;
                        return;
                    }
                }
                continue :state .impl_rhs2;
            } else {
                ErrorMsg(psp.filename, psp.tokenlineno, "" ++
                    "Expected an alias in rule impl name, got \"{s}\"", .{x});
                psp.errorcnt += 1;
                psp.state = .resync_after_impl_error;
            }
        },
        .impl_rhs2 => {
            if (x[0] == ',') {
                psp.state = .impl_rhs1;
            } else if (x[0] == ')') {
                const impl = psp.impl.?;
                if (impl.rule) |rule| {
                    if (nextNamedAliasIndex(rule.rhsalias, psp.impl_idx)) |idx| {
                        ErrorMsg(psp.filename, psp.tokenlineno, "" ++
                            "Impl \"{s}\" missing RHS alias \"{s}\".", .{
                            impl.name, rule.rhsalias[idx],
                        });
                        psp.errorcnt += 1;
                        // No resync state since we saw the )
                    }
                }
                if (psp.prevrule == null) {
                    psp.state = .waiting_for_decl_arg;
                } else {
                    psp.state = .waiting_for_decl_or_rule;
                }
            } else {
                ErrorMsg(psp.filename, psp.tokenlineno, "" ++
                    "Expected a ',' or ')', got \"{s}\" ", .{x});
                psp.errorcnt += 1;
                psp.state = .resync_after_impl_error;
            }
        },
        .lhs_alias_1 => {
            if (isAlpha(x[0])) {
                psp.lhsalias = x;
                psp.state = .lhs_alias_2;
            } else {
                ErrorMsg(psp.filename, psp.tokenlineno, "" ++
                    "\"{s}\" is not a valid alias for the LHS \"{s}\"\n", .{ x, psp.lhs.name });
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
                if (isAlpha(x[0])) {
                    ErrorMsg(psp.filename, psp.tokenlineno, "" ++
                        "Missing \"::=\" following: \"{s}({s})\".", //
                        .{ psp.lhs.name, psp.lhsalias });
                } else {
                    ErrorMsg(psp.filename, psp.tokenlineno, "" ++
                        "Expected \"::=\" following \"{s}({s})\", saw \"{s}\".", //
                        .{ psp.lhs.name, psp.lhsalias, x[0..][0..@min(x.len, 10)] });
                }
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
                errdefer rp.destroy(psp.allocator); // Frees subsequent allocations
                rp.ruleline = psp.tokenlineno;
                rp.rhs = try psp.allocator.alloc(*Symbol, psp.nrhs);
                rp.rhsalias = try psp.allocator.alloc([]const u8, psp.nrhs);
                for (0..psp.nrhs) |i| {
                    rp.rhs[i] = psp.rhs[i];
                    rp.rhsalias[i] = psp.alias[i];
                    if (rp.rhsalias[i].len > 0) rp.rhs[i].bContent = true;
                }
                rp.lhs = psp.lhs;
                rp.lhsalias = psp.lhsalias;
                dbgassert(rp.rhs.len == psp.nrhs);
                rp.noCode = true;
                dbgassert(rp.precsym == null);
                rp.index = psp.gp.nrule;
                psp.gp.nrule += 1;
                rp.nextlhs = rp.lhs.rule;
                rp.lhs.rule = rp;
                dbgassert(rp.next == null);
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
                        "Too many symbols on RHS of rule (maximum is {d}) beginning at \"{s}\".", //
                        .{ MAXRHS - 1, x });
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
                    }
                    sym_freelist = fl;
                }
                msp.subsym = try psp.allocator.realloc(msp.subsym, msp.subsym.len + 1);
                // We know x[1] exists and is terminal-shaped, so this is valid:
                msp.subsym[msp.subsym.len - 1] = try Symbol_new(x[1..]);
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
                // MAXRHS note: the resync skips all these if that value is
                // exceeded.
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
                    "Missing \")\" following LHS alias  \"{s}({s}\".", .{ psp.lhs.name, psp.lhsalias });
                psp.errorcnt += 1;
                psp.state = .resync_after_rule_error;
            }
        },
        .waiting_for_decl_keyword => {
            // This I'm doing with an enum, a StaticStringMap, and a switch.
            const decl = declarations.get(x) orelse {
                if (isAlpha(x[0])) {
                    var min_idx: usize = std.math.maxInt(usize);
                    var min_lev: usize = min_idx;
                    // Let's see if we can infer what was meant and give a nice suggestion.
                    for (directive_list, 0..) |d_entry, i| {
                        const lev = levenshtein(x, d_entry.@"0") catch std.math.maxInt(usize);
                        if (lev < min_lev) {
                            min_idx = i;
                            min_lev = lev;
                        }
                    }
                    // The ifdefs look like directives but don't switch like them, so we look at those too:
                    for (pp_list, directive_list.len..) |p_entry, i| {
                        const lev = levenshtein(x, p_entry) catch std.math.maxInt(usize);
                        if (lev < min_lev) {
                            min_idx = i;
                            min_lev = lev;
                        }
                    }
                    const suggestion = if (min_idx >= directive_list.len)
                        // Closest to a preprocessor directive.
                        pp_list[min_idx - directive_list.len]
                    else
                        // Closest to a postprocessor directive.
                        directive_list[min_idx].@"0";
                    ErrorMsg(psp.filename, psp.tokenlineno, "" ++
                        "Unknown declaration keyword: \"%{s}\".  Did you mean \"%{s}\"?", .{ x, suggestion });
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
                .impl => {
                    psp.insertLineMacro = false;
                    psp.state = .waiting_for_impl_directive;
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
                .token_enum => {
                    psp.declargslot = &psp.gp.token_enum;
                    psp.insertLineMacro = false;
                },
                .token_enum_integer => {
                    psp.declargslot = &psp.gp.token_enum_integer;
                    psp.insertLineMacro = false;
                },
                .trace_writer => {
                    psp.declargslot = &psp.gp.trace_writer;
                    psp.insertLineMacro = false;
                },
                .syntax_error => {
                    psp.declargslot = &psp.gp.@"error";
                },
                .parse_accept => {
                    psp.declargslot = &psp.gp.accept;
                },
                .parse_error_type => {
                    psp.declargslot = &psp.gp.error_type;
                    psp.insertLineMacro = false;
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
                    "Symbol name missing after %destructor directive", .{});
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
                    "Symbol name missing after %type directive", .{});
                psp.errorcnt += 1;
                psp.state = .resync_after_decl_error;
                break :state;
            }
            const sp = Symbol_find(x) orelse try Symbol_new(x);
            if (sp.datatype.len != 0) {
                ErrorMsg(psp.filename, psp.tokenlineno, "" ++
                    "Symbol %type for \"{s}\" already defined as \"{s}\"", //
                    .{ x, sp.datatype });
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
                        "Symbol \"{s}\" has already been given a precedence", .{x});
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
                // C-isms: the null sentinel, and (consequently) bare char *. So
                // idiomatic Zig looks quite different.
                var zBuffer: [64]u8 = undefined; // Line macro buffer
                // The code assumes declargslot is pointing at something, so null should be
                // unreachable here:
                const declargslot = psp.declargslot.?;
                const zOld: []const u8 = declargslot.*;
                const zNew = if (x[0] == '"' or x[0] == '{') x[1..] else x;
                const q_file = psp.gp.filename;
                var zLine: []u8 = zBuffer[0..0];
                // To build the new slice, we have to track bytes written:
                var zIdx: usize = 0;
                // The original code leaves some buffer here, because C
                // makes it difficult to count sprintf statements.  A problem
                // we do not have.
                var n = zOld.len + zNew.len;
                // Do we need a line macro?
                const addLineMacro = psp.gp.linenosflag and
                    psp.insertLineMacro and
                    (psp.decllinenoslot == null or psp.decllinenoslot.?.* != 0);
                if (addLineMacro) {
                    zLine = std.fmt.bufPrint(&zBuffer, "// #line {d} ", .{psp.tokenlineno}) catch |err| slice: {
                        // Should be literally impossible but ¯\_(ツ)_/¯
                        ErrorMsg(psp.filename, psp.tokenlineno, "" ++
                            "Buffer overflow on #line directive print: {s}", .{@errorName(err)});
                        psp.errorcnt += 1;
                        break :slice zBuffer[0..0];
                    };
                    n += zLine.len + q_file.len + 1; // newline
                    if (zOld.len > 0 and zOld[zOld.len - 1] != '\n') n += 1; // also newline
                }
                // We put this back on declargslot and PSP once we know how long the
                // slice actually should be.
                const zBuf = try psp.allocator.realloc(declargslot.*, n);
                zIdx += zOld.len;
                if (addLineMacro) {
                    if (zIdx > 0 and zBuf[zIdx - 1] != '\n') {
                        zBuf[zIdx] = '\n';
                        zIdx += 1;
                    }
                    @memcpy(zBuf[zIdx..][0..zLine.len], zLine);
                    zIdx += zLine.len;
                    @memcpy(zBuf[zIdx..][0..q_file.len], q_file);
                    zIdx += q_file.len;
                    zBuf[zIdx] = '\n';
                    zIdx += 1;
                }
                if (psp.decllinenoslot) |linenoslot| if (linenoslot.* == 0) {
                    psp.decllinenoslot.?.* = @intCast(psp.tokenlineno);
                };
                if (psp.impl) |impl| if (impl.line == 0) {
                    impl.line = psp.tokenlineno;
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
        .waiting_for_impl_directive => {
            if (x[0] == '@') {
                dbgassert(psp.impl == null);
                psp.impl = try impl_safe.get(x);
                psp.declargslot = &psp.impl.?.code;
                psp.state = .impl_1;
            } else {
                ErrorMsg(psp.filename, psp.tokenlineno, "" ++
                    "Impl name must start with @, got \"{s}\" ", .{x});
                psp.errorcnt += 1;
                psp.state = .resync_after_rule_error;
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
                } else if (sp.fallback) |sp_f| {
                    ErrorMsg(psp.filename, psp.tokenlineno, "" ++
                        "Token {s} already assigned fallback {s}", .{ sp.name, sp_f.name });
                    psp.errorcnt += 1;
                    // TODO: no resync here, is that right?
                    // yeah so it can collect more tokens
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
                if (psp.gp.wildcard) |wild| {
                    ErrorMsg(psp.filename, psp.tokenlineno, "" ++
                        "Extra wildcard {s}: already has {s}", .{ x, wild.name });
                    psp.errorcnt += 1;
                } else {
                    psp.gp.wildcard = sp;
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
                msp.subsym = subsym: {
                    if (msp.subsym.len == 0)
                        break :subsym try psp.allocator.alloc(*Symbol, 1)
                    else
                        break :subsym try psp.allocator.realloc(msp.subsym, msp.subsym.len + 1);
                };
                msp.subsym[msp.subsym.len - 1] = try Symbol_new(if (isUpper(x[0])) x else x[1..]);
            } else {
                ErrorMsg(psp.filename, psp.tokenlineno, "" ++
                    "%token_class argument \"{s}\" should be a token", .{x});
                psp.errorcnt += 1;
                psp.state = .resync_after_decl_error;
            }
        },
        .resync_after_impl_error => {
            psp.impl = null;
            if (x[0] == ')') psp.state = .waiting_for_decl_or_rule;
            continue :state .resync_after_rule_error;
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

/// Validates a pre-existing impl name, and 'repairs' the rhsalias list, which
/// may be missing un-named aliases represented as "".
fn validateAndRepairImpl(psp: *ParserState, impl: *Impl, rule: *Rule) !bool {
    if (impl.line == 0) return true;

    var good: bool = true;
    // if already defined, we need to validate the names:
    if (!mem.eql(u8, rule.lhsalias, impl.lhsalias)) {
        ErrorMsg(psp.filename, psp.tokenlineno, "" ++
            "Rule impl name is already defined, and has the LHS alias \"{s}\", " ++
            "but the rule's LHS alias is \"{s}\".  They must match", .{ impl.lhsalias, rule.lhsalias });
        psp.errorcnt += 1;
        good = false;
    }
    switch (compareRhsAliasNames(impl.rhsalias, rule.rhsalias)) {
        .match => {},
        .extra_impl => {
            ErrorMsg(psp.filename, psp.tokenlineno, "" ++
                "The impl as previously defined has more aliases than the rule", .{});
            psp.errorcnt += 1;
            good = false;
        },
        .differing => |aliases| {
            ErrorMsg(psp.filename, psp.tokenlineno, "" ++
                "Previous impl alias \"{s}\" does not match rule alias \"{s}\" ", .{
                aliases.impl_alias,
                aliases.rule_alias,
            });
            psp.errorcnt += 1;
            good = false;
            psp.state = .resync_after_rule_error;
        },
        .missing_rule => {
            ErrorMsg(psp.filename, psp.tokenlineno, "" ++
                "Rule has more aliases than impl as previously defined", .{});
            psp.errorcnt += 1;
            good = false;
            psp.state = .resync_after_rule_error;
        },
    }
    // Any old way, we copy the correct aliases, to get better errors later.
    const new_rhs = try psp.allocator.alloc([]const u8, rule.rhsalias.len);
    @memcpy(new_rhs, rule.rhsalias);
    psp.allocator.free(impl.rhsalias);
    impl.rhsalias = new_rhs;
    return good;
}

const Declaration = enum {
    code,
    default_destructor,
    default_type,
    destructor,
    extra_argument,
    extra_context,
    fallback,
    impl,
    include,
    left,
    name,
    nonassoc,
    parse_accept,
    parse_error_type,
    parse_failure,
    right,
    stack_overflow,
    stack_size,
    start_symbol,
    syntax_error,
    token_class,
    token_destructor,
    token_enum_integer,
    token_enum,
    token_type,
    token,
    trace_writer,
    type,
    wildcard,
};

const pp_list = [_][]const u8{ "ifdef", "ifndef", "if", "else", "endif" };

const directive_list = [_]struct { []const u8, Declaration }{
    .{ "name", .name },
    .{ "include", .include },
    .{ "impl", .impl },
    .{ "code", .code },
    .{ "token_destructor", .token_destructor },
    .{ "default_destructor", .default_destructor },
    .{ "token_enum", .token_enum },
    .{ "token_enum_integer", .token_enum_integer },
    .{ "trace_writer", .trace_writer },
    .{ "syntax_error", .syntax_error },
    .{ "parse_accept", .parse_accept },
    .{ "parse_error_type", .parse_error_type },
    .{ "parse_failure", .parse_failure },
    .{ "stack_overflow", .stack_overflow },
    .{ "extra_argument", .extra_argument },
    .{ "extra_context", .extra_context },
    .{ "token_type", .token_type },
    .{ "default_type", .default_type },
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

const max_cols: usize = maxcol: {
    var max: usize = 0;
    for (directive_list) |d| {
        max = @max(max, d[0].len);
    }
    break :maxcol @max(max + 1, max_opt);
};

const declarations = std.StaticStringMap(Declaration).initComptime(directive_list);

/// Lemon puts the scanner loop in `Parse`, I prefer it separate.
fn scan(ps: *ParserState, fb: [:0]const u8) !void {
    var i: usize = 0;
    var lineno: usize = 1;
    // BOM check
    if (fb.len >= 3 and fb[0] == 0xef and fb[1] == 0xbb and fb[2] == 0xbf) {
        logger.warn("Spurious BOM at head of file, skipping\n", .{});
        i = 3;
    }
    scanning: while (fb[i] != 0) {
        var skip: bool = false; // True when we advance one more before loop
        if (fb[i] == '\n') lineno += 1;
        if (isSpace(fb[i])) {
            i += 1;
            continue :scanning;
        } // Skip all whitespace
        // Skip comments
        if (fb[i] == '/' and fb[i + 1] == '/') {
            i += 2;
            while (fb[i] != '\n' and fb[i] != 0) : (i += 1) {}
            if (fb[i] != 0) {
                if (fb[i] == '\n') lineno += 1;
                i += 1;
                continue :scanning;
            } else break :scanning;
        }
        // Skip C style comments (this is in the grammar file, not code)
        if (fb[i] == '/' and fb[i + 1] == '*') {
            i += 2;
            if (fb[i] == 0) break :scanning;
            if (fb[i] == '*') i += 1;
            if (fb[i] == 0) break :scanning;
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
        } else if (fb[i] == '{') { // A block of Zig code
            var level: usize = 1;
            i += 1;
            codescan: while (fb[i] != 0 and (level > 1 or fb[i] != '}')) : (i += 1) {
                if (fb[i] == '\n') lineno += 1 //
                else if (fb[i] == '{') level += 1 //
                else if (fb[i] == '}') level -= 1 //
                else if (fb[i] == '\\' and fb[i + 1] == '\\') {
                    // Skip multiline strings
                    i += 2;
                    while (fb[i] != '\n' and fb[i] != 0) : (i += 1) {}
                    if (fb[i] != 0) {
                        if (fb[i] == '\n') lineno += 1;
                        i += 1;
                        continue :codescan;
                    } else break :scanning;
                } else if (fb[i] == '/' and fb[i + 1] == '/') {
                    // Skip comments
                    i += 2;
                    while (fb[i] != 0 and fb[i] != '\n') : (i += 1) {}
                    if (fb[i] == '\n') {
                        lineno += 1;
                        continue :codescan;
                    } else { // EOF
                        ErrorMsg(ps.filename, ps.tokenlineno, "" ++
                            "Zig comment on this line ends file unexpectedly", .{});
                        ps.errorcnt += 1;
                        break :scanning;
                    }
                } else if (fb[i] == '"' or fb[i] == '\'') {
                    // String or character literals (since the latter can have " in it)
                    const startchar = fb[i];
                    var prevc: u8 = 0;
                    i += 1;
                    while (fb[i] != 0 and (fb[i] != startchar or prevc == '\\')) : (i += 1) {
                        if (fb[i] == '\n') {
                            ErrorMsg(ps.filename, ps.tokenlineno, "" ++
                                "Zig code on this line contains an un-terminated string, or " ++
                                "botched character literal.", .{});
                            ps.errorcnt += 1;
                            // Line number is incremented here:
                            continue :scanning;
                        }
                        if (prevc == '\\')
                            prevc = 0
                        else
                            prevc = fb[i]; // clever
                    }
                }
            }
            if (i == fb.len and fb[i - 1] != '}') {
                ErrorMsg(ps.filename, ps.tokenlineno, "" ++
                    "Zig code starting on this line is not terminated before " ++
                    "the end of the file.", .{});
                ps.errorcnt += 1;
            } else {
                skip = true; // Clip end of C blocks also
            }
        } else if (isAlnum(fb[i]) or fb[i] == '@') {
            i += 1;
            while (fb[i] != 0 and (isAlnum(fb[i]) or fb[i] == '_')) : (i += 1) {}
        } else if (i + 2 < fb.len and fb[i] == ':' and fb[i + 1] == ':' and fb[i + 2] == '=') {
            i += 3;
        } else if (fb[i] == '/' or fb[i] == '|' and isAlpha(fb[i + 1])) {
            i += 2;
            while (fb[i] != 0 and (isAlnum(fb[i]) or fb[i] == '_')) : (i += 1) {}
        } else if (fb[i] == '`' and fb[i + 1] == '`') { // 'Ditto' operator
            i += 2;
        } else { //  All other (one character) operators
            i += 1;
            // While far from perfect, consuming a full code point will
            // give better error messages in many circumstances:
            while (0x80 <= fb[i] and fb[i] < 0xc0) : (i += 1) {}
        }
        const x = fb[ps.tokenstart..i];
        if (p_print) std.debug.print("i == {d} '{u}' ", .{ i, fb[i] });
        try parseonetoken(ps, x);
        if (p_print) std.debug.print("skip: {any} ", .{skip});
        if (skip) i += 1; // End byte of string and code tokens.
    }
}

//| Nicer error messages

/// Return the Levenshtein edit distance between two slices.
fn levenshtein(a_in: []const u8, b_in: []const u8) !usize {
    var a = a_in;
    var b = b_in;
    if (a.len > b.len) {
        // Ensure a is the shorter side
        b = a_in;
        a = b_in;
    }

    const cols = a.len + 1;

    var p_buf: [max_cols]u16 = undefined;
    var c_buf: [max_cols]u16 = undefined;
    var prev = p_buf[0..cols];
    var curr = c_buf[0..cols];

    // Initialize prev row: distance from empty prefix of b to prefixes of a
    // prev[j] = j
    for (prev, 0..) |*p, j| p.* = @truncate(j);

    // DP over rows of b
    for (b, 0..) |bch, i_idx| {
        const i: u16 = @truncate(i_idx + 1);
        curr[0] = i; // distance from first i bytes of b to empty a

        // Fill row
        var j: usize = 1;
        while (j < cols) : (j += 1) {
            const cost: usize = if (a[j - 1] == bch) 0 else 1;
            const del = prev[j] + 1; // delete from b
            const ins = curr[j - 1] + 1; // insert into b
            const sub = prev[j - 1] + cost; // substitute
            curr[j] = @min(del, @min(ins, sub));
        }

        // Swap rows
        const tmp = prev;
        prev = curr;
        curr = tmp;
    }

    return prev[cols - 1];
}

/// Reduce the size of the action tables, if possible, by making use
/// of defaults.
///
/// In this version, we take the most frequent REDUCE action and make
/// it the default.  Except, there is no default if fallback or wildcard
/// selection could observe a removed action.
fn CompressTables(zyt: *Zitron) !void {
    states: for (zyt.sorted) |stp| {
        var nbest: usize = 0;
        var rbest: ?*Rule = null;
        var usesFallback = false;
        var usesWildcard = false;
        var m_ap: ?*Action = stp.ap;
        actions: while (m_ap) |ap| : (m_ap = ap.next) {
            if (ap.type == .reduce and ap.sp.fallback != null) {
                usesFallback = true;
            }
            if (ap.sp == zyt.wildcard and
                (ap.type == .shift or ap.type == .reduce or
                    ap.type == .@"error" or ap.type == .accept))
            {
                usesWildcard = true;
            }
            if (ap.type != .reduce) continue :actions;
            const rp = ap.x.rp.?; // Always rule on .reduce
            if (rp.lhsStart) continue :actions;
            if (rp == rbest) continue :actions;
            var n: usize = 1;
            var m_ap2 = ap.next;
            next_act: while (m_ap2) |ap2| : (m_ap2 = ap2.next) {
                if (ap2.type != .reduce) continue :next_act;
                const rp2 = ap2.x.rp.?;
                if (rp2 == rbest) continue :next_act;
                if (rp2 == rp) n += 1;
            }
            if (n > nbest) {
                nbest = n;
                rbest = rp;
            }
            // Do not make a default if the number of rules to default
            // is not at least 1 or if a selector could observe it.
            //
        }
        if (nbest < 1 or usesFallback or usesWildcard) continue :states;

        if (p_check1) dprint("can optimize State {d}\n", .{stp.statenum});

        if (p_check1) {
            m_ap = stp.ap;
            const stderr = std.io.getStdErr().writer();
            while (m_ap) |ap| : (m_ap = ap.next) {
                _ = try PrintAction(stderr, ap, 0, zyt.opt.show_conflicts);
            }
            m_ap = stp.ap;
        }
        // Combine matching REDUCE actions into a single default.
        m_ap = stp.ap;
        while (m_ap) |ap| : (m_ap = ap.next) {
            if (ap.type == .reduce and ap.x.rp == rbest) break;
        }
        dbgassert(m_ap != null);
        if (p_check1) dprint("old symbol name {s}\n", .{m_ap.?.sp.name});
        m_ap.?.sp = zyt.symbols[zyt.nsymbol];
        dbgassert(strcmp(m_ap.?.sp.name, "{default}"));
        if (p_check1) dprint("new symbol name {s}\n", .{m_ap.?.sp.name});
        m_ap = m_ap.?.next;
        while (m_ap) |ap| : (m_ap = ap.next) {
            if (ap.type == .reduce and ap.x.rp == rbest) {
                ap.type = .not_used;
            }
        }
        stp.ap = if (stp.ap) |ap| Action.sort(ap) else null;
        m_ap = stp.ap;

        while (m_ap) |ap| : (m_ap = ap.next) {
            if (ap.type == .shift) break;
            if (ap.type == .reduce and ap.x.rp != rbest) break;
        } else {
            stp.autoreduce = true;
            stp.pDefltReduce = rbest;
        }
    }
    // Make a second pass over all states and actions.  Convert
    // every action that is a SHIFT to an autoReduce state into
    // a SHIFTREDUCE action.
    for (zyt.sorted) |stp| {
        var m_ap: ?*Action = stp.ap;
        actions: while (m_ap) |ap| : (m_ap = ap.next) {
            if (ap.type != .shift) continue :actions;
            const pNextState = ap.x.stp;
            if (pNextState.autoreduce and pNextState.pDefltReduce != null) {
                ap.type = .shiftreduce;
                ap.x = .{ .rp = pNextState.pDefltReduce };
            }
        }
    }
    // If a SHIFTREDUCE action specifies a rule that has a single RHS term
    // (meaning that the SHIFTREDUCE will land back in the state where it
    // started) and if there is no C-code associated with the reduce action,
    // then we can go ahead and convert the action to be the same as the
    // action for the RHS of the rule.
    //
    for (zyt.sorted) |stp| {
        var m_ap: ?*Action = stp.ap;
        var nextap: ?*Action = null;
        actions: while (m_ap) |ap| : (m_ap = nextap) {
            nextap = ap.next;
            if (ap.type != .shiftreduce) continue :actions;
            const rp = ap.x.rp.?;
            if (!rp.noCode) continue :actions;
            if (rp.rhs.len != 1) continue :actions;
            if (comptime do_not_optimize_terminals) {
                // Only apply this optimization to non-terminals.  It would be OK to
                // apply it to terminal symbols too, but that makes the parser tables
                // larger.
                if (ap.sp.index < zyt.nterminal) continue :actions;
            }
            // If we reach this point, it means the optimization can be applied
            nextap = ap;
            var m_ap2 = stp.ap;
            while (m_ap2 != null and
                (m_ap2 == ap or m_ap2.?.sp != rp.lhs)) : (m_ap2 = m_ap2.?.next)
            {}
            dbgassert(m_ap2 != null);
            const ap2 = m_ap2.?;
            ap.spOpt = ap2.sp;
            ap.type = ap2.type;
            ap.x = ap2.x;
        }
    }
}

//
// Compare two states for sorting purposes.  The smaller state is the
// one with the most non-terminal actions.  If they have the same number
// of non-terminal actions, then the smaller is the one with the most
// token actions.
fn stateResortCompare(_: void, pA: *State, pB: *State) bool {
    if (pA.nNtAct > pB.nNtAct) return true;
    if (pA.nNtAct < pB.nNtAct) return false;
    if (pA.nTknAct > pB.nTknAct) return true;
    if (pA.nTknAct < pB.nTknAct) return false;
    if (pA.statenum > pB.statenum) return true;
    if (pA.statenum <= pB.statenum) return false;
    unreachable;
}

const NO_OFFSET = -2147483647;

//
// Renumber and resort states so that states with fewer choices
// occur at the end.  Except, keep state 0 as the first state.
//
fn ResortStates(zyt: *Zitron) void {
    for (zyt.sorted) |stp| {
        if (p_check1) {
            dprint("state before resort: {d}\n", .{stp.statenum});
        }
        stp.nTknAct = 0;
        stp.nNtAct = 0;
        stp.iDfltReduce = -1; //  Init dflt action to "syntax error"
        stp.iTknOfst = NO_OFFSET;
        stp.iNtOfst = NO_OFFSET;
        var m_ap = stp.ap;
        while (m_ap) |ap| : (m_ap = ap.next) {
            const m_iAction = compute_action(zyt, ap);
            if (m_iAction) |iAction| {
                if (ap.sp.index < zyt.nterminal) {
                    stp.nTknAct += 1;
                } else if (ap.sp.index < zyt.nsymbol) {
                    stp.nNtAct += 1;
                } else {
                    dbgassert(!stp.autoreduce or stp.pDefltReduce == ap.x.rp);
                    stp.iDfltReduce = @intCast(iAction);
                }
            }
        }
    }
    std.mem.sort(*State, zyt.sorted[1..], {}, stateResortCompare);
    for (zyt.sorted, 0..) |stp, i| {
        if (p_check1) {
            dprint("statenum was #{d}, now #{d}\n", .{ stp.statenum, i });
        }
        stp.statenum = @intCast(i);
    }
    zyt.nxstate = zyt.nstate;
    while (zyt.nxstate > 1 and zyt.sorted[zyt.nxstate - 1].autoreduce) {
        zyt.nxstate -= 1;
    }
}

// Given an action, compute the integer value for that action
// which is to be put in the action table of the generated machine.
// Return negative if no action should be generated.
fn compute_action(zyt: *Zitron, ap: *Action) ?u32 {
    return act: switch (ap.type) {
        .shift => break :act ap.x.stp.statenum,
        .shiftreduce => {
            // Since a SHIFT is inherent after a prior REDUCE, convert any
            // SHIFTREDUCE action with a nonterminal on the LHS into a simple
            // REDUCE action:
            if (ap.sp.index >= zyt.nterminal and
                (zyt.errsym == null or ap.sp.index != zyt.errsym.?.index))
            {
                break :act zyt.minReduce + ap.x.rp.?.iRule;
            } else {
                break :act zyt.minShiftReduce + ap.x.rp.?.iRule;
            }
        },
        .reduce => break :act zyt.minReduce + ap.x.rp.?.iRule,
        .@"error" => break :act zyt.errAction,
        .accept => break :act zyt.accAction,
        else => break :act null,
    };
}

/// Compute the action table, but do not output it yet.  The action
/// table must be computed before generating the YYNSTATE macro because
/// we need to know how many states can be eliminated.
fn Compute_actiontable(zyt: *Zitron) !*ActTable {
    const ax = try zyt.allocator.alloc(AxSet, zyt.nxstate * 2);
    defer zyt.allocator.free(ax);
    @memset(ax, .empty);
    for (0..zyt.nxstate) |i| {
        const stp = zyt.sorted[i];
        const ix2 = 2 * i;
        ax[ix2].stp = stp;
        ax[ix2].isTkn = true;
        ax[ix2].nAction = stp.nTknAct;
        ax[ix2 + 1].stp = stp;
        ax[ix2 + 1].isTkn = false; // redundant
        ax[ix2 + 1].nAction = stp.nNtAct;
    }
    var mxTknOfst: int, var mnTknOfst: int = .{ 0, 0 };
    var mxNtOfst: int, var mnNtOfst: int = .{ 0, 0 };
    // In an effort to minimize the action table size, use the heuristic
    // of placing the largest action sets first */
    for (0..zyt.nxstate * 2) |i| ax[i].iOrder = @intCast(i);
    mem.sort(AxSet, ax, {}, axset_compare);
    if (p_check1) {
        dprint("Action table: ", .{});
        for (ax) |an_x| {
            dprint("{d} ", .{an_x.iOrder});
        }
        dprint("\n", .{});
        dprint("nterminal {d} nsymbol {d}\n", .{ zyt.nterminal, zyt.nsymbol });
    }
    const pActtab = try ActTable.create(zyt.allocator, zyt.nsymbol, zyt.nterminal);
    errdefer pActtab.destroy();
    var i: usize = 0;
    while (i < zyt.nxstate * 2 and ax[i].nAction > 0) : (i += 1) {
        const stp = ax[i].stp;
        if (ax[i].isTkn) {
            var m_ap: ?*Action = stp.ap;
            var j: usize = 0;
            actions: while (m_ap) |ap| : (m_ap = ap.next) {
                if (ap.sp.index >= zyt.nterminal) continue :actions;
                if (p_check1) j += 1;
                if (p_debug) dprint("adding >= nterminal type {s}\n", .{@tagName(ap.type)});
                const m_action = compute_action(zyt, ap);
                if (m_action) |action| {
                    try pActtab.action(ap.sp.index, @intCast(action));
                }
            }
            if (p_check1) {
                dprint("token: State {d} with {d} actions\n", .{ stp.statenum, j });
            }
            stp.iTknOfst = try pActtab.insert(true);
            if (stp.iTknOfst < mnTknOfst) mnTknOfst = stp.iTknOfst;
            if (stp.iTknOfst > mxTknOfst) mxTknOfst = stp.iTknOfst;
        } else {
            var j: usize = 0;
            var m_ap: ?*Action = stp.ap;
            if (p_check1) {
                dprint("nonterminal action list:", .{});
            }
            actions: while (m_ap) |ap| : (m_ap = ap.next) {
                if (p_check1) {
                    dprint(" {s}", .{ap.sp.name});
                }
                if (ap.sp.index < zyt.nterminal) continue :actions;
                if (ap.sp.index == zyt.nsymbol) continue :actions;
                if (p_check1) j += 1;
                if (p_debug) dprint("adding < nterminal type {s}\n", .{@tagName(ap.type)});
                const m_action = compute_action(zyt, ap);
                if (m_action) |action| {
                    try pActtab.action(ap.sp.index, @intCast(action));
                }
            }
            if (p_check1) {
                dprint("\n nonterminal: State {d} with {d} actions\n", .{ stp.statenum, j });
            }
            stp.iNtOfst = try pActtab.insert(false);
            if (stp.iNtOfst < mnNtOfst) mnNtOfst = stp.iNtOfst;
            if (stp.iNtOfst > mxNtOfst) mxNtOfst = stp.iNtOfst;
        }
        if (p_check1) {
            var nn: usize = 0;
            for (pActtab.aAction[0..pActtab.nAction]) |act_tab| {
                if (act_tab.action < 0) nn += 1;
            }
            dprint(
                "{d:>4}: State {d:>3} {s} n: {d:>2} size: {d:>5} freespace: {d}\n",
                .{
                    i,
                    stp.statenum,
                    if (ax[i].isTkn) "Token" else "Var  ",
                    ax[i].nAction,
                    pActtab.nAction,
                    nn,
                },
            );
        }
    }
    pActtab.mnTknOfst = mnTknOfst;
    pActtab.mxTknOfst = mxTknOfst;
    pActtab.mnNtOfst = mnNtOfst;
    pActtab.mxNtOfst = mxNtOfst;
    return pActtab;
}

const Options = struct {
    allocator: Allocator = undefined,
    help: bool = false,
    version: bool = false,
    grammar: bool = config.grammar,
    enum_file: bool = config.enum_file,
    no_compress: bool = config.no_compress,
    fifo: bool = false,
    print_pp: bool = false,
    linenos: bool = config.line_numbers,
    show_conflicts: bool = config.show_conflicts,
    clean_exit: bool = config.clean_exit,
    quiet: bool = config.quiet,
    statistics: bool = config.statistics,
    sql_flag: bool = config.sql,
    only_basis: bool = config.only_basis,
    no_resort: bool = config.no_resort,
    unbundle: bool = config.unbundle,
    user_templatename: []const u8 = "",
    output_directory: []const u8 = "",
    output_file: []const u8 = "",
    azDefine: [][]const u8 = undefined,
    nDefineUsed: u32 = 0,
    bDefineUsed: []bool = undefined,

    pub fn deinit(o: *Options, alloc: Allocator) void {
        alloc.free(o.azDefine);
        alloc.free(o.bDefineUsed);
    }
};

const OptionKind = enum {
    help,
    version,
    grammar,
    enum_file,
    no_compress,
    fifo,
    print_pp,
    linenos,
    show_conflicts,
    clean_exit,
    quiet,
    statistics,
    sql_flag,
    only_basis,
    no_resort,
    unbundle,
    user_template,
    output_directory,
    output_file,
    define,
    undefine,

    pub fn shortOpt(b: u8) ?OptionKind {
        return switch (b) {
            'b' => .only_basis,
            'C' => .show_conflicts,
            'c' => .no_compress,
            'd' => .output_directory,
            'D' => .define,
            'e' => .enum_file,
            'F' => .fifo,
            'f' => .output_file,
            'g' => .grammar,
            'h' => .help,
            'l' => .linenos,
            'P' => .print_pp,
            'q' => .quiet,
            'r' => .no_resort,
            's' => .statistics,
            'S' => .sql_flag,
            'T' => .user_template,
            'u' => .unbundle,
            'U' => .undefine,
            'v' => .version,
            'x' => .clean_exit,
            else => null,
        };
    }

    pub fn takesArgument(ok: OptionKind) bool {
        return switch (ok) {
            .help,
            .version,
            .grammar,
            .enum_file,
            .no_compress,
            .fifo,
            .print_pp,
            .linenos,
            .show_conflicts,
            .clean_exit,
            .quiet,
            .statistics,
            .sql_flag,
            .only_basis,
            .no_resort,
            .unbundle,
            => false,
            .user_template,
            .output_directory,
            .output_file,
            .define,
            .undefine,
            => true,
        };
    }
};

const option_list = [_]struct { []const u8, OptionKind }{
    .{ "help", .help },
    .{ "version", .version },
    .{ "grammar", .grammar },
    .{ "enum-file", .enum_file },
    .{ "no-compress", .no_compress },
    .{ "fifo", .fifo },
    .{ "pp-only", .print_pp },
    .{ "line-numbers", .linenos },
    .{ "show-conflicts", .show_conflicts },
    .{ "clean-exit", .clean_exit },
    .{ "quiet", .quiet },
    .{ "statistics", .statistics },
    .{ "sql", .sql_flag },
    .{ "only-basis", .only_basis },
    .{ "no-resort", .no_resort },
    .{ "unbundle", .unbundle },
    .{ "template", .user_template },
    .{ "directory", .output_directory },
    .{ "file", .output_file },
    .{ "define", .define },
    .{ "undefine", .undefine },
};

const opt_map = std.StaticStringMap(OptionKind).initComptime(option_list);

const max_opt: usize = maxopt: {
    var max: usize = 0;
    for (option_list) |o| {
        max = @max(max, o[0].len);
    }
    break :maxopt max + 1;
};

/// Return the argument of an option which takes one, or a
/// useful error otherwise.
fn optionArgument(args: []const [:0]const u8, n: *usize, i: *usize) ![:0]const u8 {
    if (i.* < args[n.*].len - 1) {
        if (args[n.*][i.* + 1] == '=') {
            if (i.* + 2 < args[n.*].len) {
                const start = i.* + 2;
                i.* = args[n.*].len;
                return args[n.*][start.. :0];
            } else {
                i.* += 1;
                return error.MissingArgumentAfterEquals;
            }
        } else {
            return error.NoEqualsAfterOption;
        }
    } else if (n.* < args.len - 1) {
        n.* += 1;
        if (args[n.*][0] == '-') return error.MissingArgument;
        return args[n.*];
    } else {
        return error.OutOfArguments;
    }
}

/// Print the command line with a caret pointing to the k-th character
/// of the n-th field.
fn errline(args: []const [:0]const u8, n: usize, k: usize) void {
    var spcnt: usize = 0;
    var i: usize = 0;

    if (args.len > 0) {
        const idx = if (mem.lastIndexOfScalar(u8, args[0], '/')) |id| id + 1 else 0;
        std.debug.print("{s}", .{args[0][idx..]});
        spcnt = args[0][idx..].len + 1;
        i = 1;
    } else {
        spcnt = 0;
    }

    while (i < n and i < args.len) : (i += 1) {
        std.debug.print(" {s}", .{args[i]});
        spcnt += args[i].len + 1;
    }

    spcnt += k;

    while (i < args.len) : (i += 1) {
        std.debug.print(" {s}", .{args[i]});
    }

    if (spcnt < 20) {
        // `.s` can be anything, not related to s: (funky fmt parser)
        std.debug.print("\n{s: >[len]}^-- here\n\n", .{ .s = "", .len = spcnt });
    } else {
        const adj = spcnt - 7;
        std.debug.print("\n{s: >[len]}here --^\n\n", .{ .s = "", .len = adj });
    }
}

fn assignArgument(opt: *Options, opt_kind: OptionKind, argument: [:0]const u8) !void {
    switch (opt_kind) {
        .user_template => {
            opt.user_templatename = try Strsafe(argument);
        },
        .output_directory => {
            opt.output_directory = try Strsafe(argument);
        },
        .output_file => {
            opt.output_file = try Strsafe(argument);
        },
        .define => {
            for (opt.azDefine) |d| {
                if (strcmp(d, argument)) return;
            }
            const safe_arg = try Strsafe(argument);
            opt.azDefine = try opt.allocator.realloc(opt.azDefine, opt.azDefine.len + 1);
            opt.azDefine[opt.azDefine.len - 1] = safe_arg;
            opt.bDefineUsed = try opt.allocator.realloc(opt.bDefineUsed, opt.bDefineUsed.len + 1);
            opt.bDefineUsed[opt.bDefineUsed.len - 1] = false;
        },
        .undefine => {
            for (opt.azDefine, 0..) |def, i| {
                if (strcmp(def, argument)) {
                    // Clobber with the last value (aliasing is harmless)
                    opt.azDefine[i] = opt.azDefine[opt.azDefine.len - 1];
                    opt.bDefineUsed[i] = opt.bDefineUsed[opt.bDefineUsed.len - 1];
                    opt.azDefine = try opt.allocator.realloc(opt.azDefine, opt.azDefine.len - 1);
                    opt.bDefineUsed = try opt.allocator.realloc(opt.bDefineUsed, opt.bDefineUsed.len - 1);
                }
            }
        },
        else => |k| {
            std.debug.panic("Option {t} does not take argument (internal error)", .{k});
        },
    }
}

fn assignFlag(opt: *Options, opt_kind: OptionKind) void {
    switch (opt_kind) {
        .help => opt.help = true,
        .version => opt.version = true,
        .grammar => opt.grammar = !opt.grammar,
        .enum_file => opt.enum_file = !opt.enum_file,
        .no_compress => opt.no_compress = !opt.no_compress,
        .fifo => opt.fifo = true,
        .print_pp => opt.print_pp = !opt.print_pp,
        .linenos => opt.linenos = !opt.linenos,
        .show_conflicts => opt.show_conflicts = !opt.show_conflicts,
        .clean_exit => opt.clean_exit = !opt.clean_exit,
        .quiet => opt.quiet = !opt.quiet,
        .statistics => opt.statistics = !opt.statistics,
        .sql_flag => opt.sql_flag = !opt.sql_flag,
        .only_basis => opt.only_basis = !opt.only_basis,
        .no_resort => opt.no_resort = !opt.no_resort,
        .unbundle => opt.unbundle = !opt.unbundle,
        else => |k| std.debug.panic("Option {t} is not a flag (internal error)", .{k}),
    }
}

fn readShortArgs(opt: *Options, args: []const [:0]const u8, n: *usize, i: *usize) !void {
    dbgassert(n.* < args.len);
    dbgassert(i.* == 1);
    const arg = args[n.*];
    while (i.* < arg.len) : (i.* += 1) {
        const opt_kind = OptionKind.shortOpt(arg[i.*]) orelse return error.ShortOptionNotRecognized;
        if (opt_kind.takesArgument()) {
            const argument = try optionArgument(args, n, i);
            try assignArgument(opt, opt_kind, argument);
        } else {
            if (i.* < arg.len - 1 and arg[i.* + 1] == '=') {
                return error.SwitchTakesNoArgument;
            }
            assignFlag(opt, opt_kind);
        }
    }
}

fn readLongArg(opt: *Options, args: []const [:0]const u8, n: *usize, i: *usize) !void {
    dbgassert(n.* < args.len);
    dbgassert(i.* == 2);
    const arg = args[n.*];
    const start = i.*;
    while (i.* < arg.len and arg[i.*] != '=') : (i.* += 1) {}
    const long = arg[start..i.*];
    const opt_kind = opt_map.get(long) orelse return error.LongOptionNotRecognized;
    if (opt_kind.takesArgument()) {
        const argument = try optionArgument(args, n, i);
        try assignArgument(opt, opt_kind, argument);
    } else {
        if (i.* < arg.len) {
            // Argument where none expected:
            dbgassert(arg[i.*] == '=');
            return error.SwitchTakesNoArgument;
        }
        assignFlag(opt, opt_kind);
    }
}

fn readOneArg(opt: *Options, args: []const [:0]const u8, n: *usize, i: *usize) !bool {
    dbgassert(n.* < args.len);
    const arg = args[n.*];
    if (arg[0] != '-') return false; // Presumably the file name.
    if (args[n.*].len < 2) return error.ArgTooShort;
    if (arg[1] == '-') {
        // dash-dash?
        if (arg.len == 2) {
            n.* += 1;
            return false;
        }
        i.* = 2;
        try readLongArg(opt, args, n, i);
    } else {
        i.* = 1;
        try readShortArgs(opt, args, n, i);
    }
    return true;
}

/// Quiet other file outputs in fifo mode.
fn fixupDependentOptions(opt: *Options) void {
    if (opt.fifo) {
        opt.sql_flag = false;
        opt.enum_file = false;
        opt.quiet = true;
    }
}

/// Initialize the Options struct.  Return the index at which the filename should be
/// found
fn optionsInit(opt: *Options, args: []const [:0]const u8, allocator: Allocator) !usize {
    opt.allocator = allocator;
    if (config.define) |defines| {
        const n = opt.azDefine.len;
        opt.azDefine = try allocator.alloc([]const u8, n + defines.len);
        opt.bDefineUsed = try allocator.alloc(bool, n + defines.len);
        dbgassert(opt.azDefine.len == opt.bDefineUsed.len);
        for (defines, 0..) |d, i| {
            opt.azDefine[n + i] = d;
            opt.bDefineUsed[n + i] = false;
        }
    } else {
        opt.azDefine = try allocator.alloc([]const u8, 0);
        opt.bDefineUsed = try allocator.alloc(bool, 0);
    }
    var errcnt: usize = 0;
    var last_err: usize = 0;
    var n: usize = 1;
    var i: usize = 0;
    while (n < args.len) : (n += 1) {
        const more = readOneArg(opt, args, &n, &i) catch |err| more: {
            if (err == error.OutOfMemory) return err;
            if (last_err == 0) dprint("Error in command line arguments:\n", .{});
            errcnt += 1;
            last_err = errcnt;
            switch (err) {
                error.OutOfMemory => unreachable,
                error.ArgTooShort => {
                    dprint("  - \"-\" is not an argument (missing flag?):\n", .{});
                },
                error.SwitchTakesNoArgument => {
                    dprint("  - This switch takes no argument:\n", .{});
                },
                error.LongOptionNotRecognized => {
                    var min_idx: usize = 0;
                    var min_lev: usize = std.math.maxInt(usize);
                    for (option_list, 0..) |o_entry, idx| {
                        const lev = levenshtein(args[n][2..], o_entry.@"0") catch std.math.maxInt(usize);
                        if (lev < min_lev) {
                            min_idx = idx;
                            min_lev = lev;
                        }
                    }
                    dprint(
                        "  - Long option not recognized: '{s}', did you mean '--{s}'?\n",
                        .{ args[n], option_list[min_idx].@"0" },
                    );
                    i = 0;
                },
                error.ShortOptionNotRecognized => {
                    dprint("  - Short option not recognized:\n", .{});
                },
                error.NoEqualsAfterOption, error.OutOfArguments => {
                    dprint("  - This option must be followed by an argument:\n", .{});
                },
                error.MissingArgument => {
                    dprint("  - Option is missing its argument:\n", .{});
                    n -= 1;
                },
                error.MissingArgumentAfterEquals => {
                    dprint("  - Option is missing its argument:\n", .{});
                },
            }
            errline(args, n, i);
            break :more true;
        };
        if (!more) break;
        i = 0;
    }
    if (errcnt > 0) {
        dprint("Try `{s} --help` to print valid options.\n", .{shortProgramName(args)});
        exit(1);
    }
    fixupDependentOptions(opt);
    return n;
}

fn shortProgramName(args: []const [:0]const u8) []const u8 {
    const idx = if (mem.lastIndexOfScalar(u8, args[0], '/')) |slash| slash + 1 else 0;
    return args[0][idx..];
}

// TODO: something better here
const help_string =
    \\
    \\ {s} [opts] [--] filename.zy
    \\
    \\ Options:
    \\
    \\   -b, --basis               Show only the basis for each parser state in the report file.
    \\   -c, --no-compress         Do not compress the generated action tables. The parser will be
    \\                             a little larger and slower, but it will detect syntax errors sooner.
    \\   -d, --directory directory Write all output files into "directory". Normally,
    \\                             output files are written into the directory that contains the input
    \\                             grammar file.
    \\   -D, --define name         Define C-like preprocessor macro "name".  This macro is usable
    \\                             by %ifdef, %ifndef, and %if lines in the grammar file.
    \\                             It is legal to define a name more than once.
    \\   -e --enum-file            Emit the token enum as its own file.
    \\   -F --fifo                 Read grammar from standard input and write Zig to standard output.
    \\   -f --file file            Write the file(s) using this name instead.
    \\   -g --grammar              Do not generate a parser.  Instead write the input grammar to
    \\                             standard output with all comments, actions, and other extraneous
    \\                             text removed.
    \\   -l --lines                Add "// #line" comments in the generated parser's Zig code.
    \\   -P --pp-only              Run the "%if" preprocessor step only and print the revised
    \\                             grammar file.
    \\   -p --precedence           Display all conflicts that are resolved by [precedence rules].
    \\   -q --quiet                Suppress generation of the report file.
    \\   -r --no-renumber          Do not sort or renumber the parser states as part of
    \\                             optimization.
    \\   -s --show-stats           Show parser statistics before exiting.
    \\   -S --sql                  Generate the *.sql file describing the parser tables.
    \\   -T, --template file       Use "file" as the template for the generated Zig
    \\                             parser implementation.
    \\   -u, --unbundle            Do not bundle identical generated code blocks.
    \\   -U, --undefine name       Undefine C-like preprocessor macro "name".  It is legal to
    \\                             undefine a nonexistent name.
    \\   -v, --version             Print the Zitron version number.
    \\   -x, --clean-exit          Always exit with code 0, despite errors.
;

fn OptPrint(out: anytype, args: []const [:0]const u8) !void {
    try out.print(help_string, .{shortProgramName(args)});
}

fn strLessThan(_: void, a: []const u8, b: []const u8) bool {
    if (a.len < b.len) return true;
    if (b.len < a.len) return false;
    for (a, b) |ac, bc| {
        if (ac < bc) return true;
        if (ac > bc) return false;
    }
    return false; // Equal is not less than
}

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

/// Add a new element to the set.  Return `true` if the element was added
/// and `false` if it was already there.
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

/// Print a statistic to the provided Writer.
fn stats_line(in: anytype, zLabel: []const u8, iValue: usize) !void {
    try in.print("  {s}", .{zLabel});
    try in.splatByteAll('.', 35 - zLabel.len);
    try in.print(" {d: >5}\n", .{iValue});
}

fn warmup(allocator: Allocator) !void {
    // Set up pools.
    action_allocator = .init(allocator);
    Configlist_init(allocator, .init(allocator));
    cf_ls.allocator = allocator;
    plink_freelist = .init(allocator);
    is_plink_freelist = true;
    try plink_freelist.addCapacity(100);
    errdefer Plink_deinit();
    Strsafe_init(allocator);
    Symbol_init(allocator);
    try State_init(allocator);
    impl_safe = .init(allocator);
    errdefer comptime unreachable;
}

fn teardown(allocator: Allocator) void {
    // Some rare symbols 'spill', because they can't be
    // stored in the Symbol intern map, we we free those
    // here.
    while (sym_freelist) |free| {
        free.sp.destroy(allocator);
        sym_freelist = free.next;
        allocator.destroy(free);
    }

    State_free();
    Symbol_free();
    Strsafe_free();
    Plink_deinit();
    is_plink_freelist = false;
    Configlist_deinit();
    impl_safe.deinit();
    action_allocator.deinit();
}

pub fn main(init: std.process.Init) !void {
    var gpa = gpa: {
        if (is_debug) {
            const dbgpa: std.heap.DebugAllocator(.{ .stack_trace_frames = 10 }) = .init;
            break :gpa dbgpa;
        } else {
            break :gpa std.heap.smp_allocator;
        }
    };
    defer {
        if (is_debug) assert(.ok == gpa.deinit());
    }
    const allocator = if (is_debug) gpa.allocator() else gpa;
    try warmup(allocator);
    defer teardown(allocator);

    const args = try init.minimal.args.toSlice(allocator);
    defer allocator.free(args);
    var opt: Options = .{};
    defer opt.deinit(allocator);
    const file_index = init_opts: {
        break :init_opts try optionsInit(&opt, args, allocator);
    };
    // A few more syscalls, but I'd rather not fatten the stack
    var stdout_buffer: [128]u8 = undefined;
    if (opt.help) {
        var stdout_writer = std.Io.File.stdout().writer(init.io, &stdout_buffer);
        const stdout = &stdout_writer.interface;
        try OptPrint(stdout, args);
        stdout.flush() catch {};
        exit(0);
    }
    if (opt.version) {
        var stdout_writer = std.Io.File.stdout().writer(init.io, &stdout_buffer);
        const stdout = &stdout_writer.interface;
        stdout.print("{s} version 0.2.7\n", .{shortProgramName(args)}) catch {};
        stdout.flush() catch {};
        exit(0);
    }
    if (file_index != args.len - 1) {
        dprint("Exactly one filename argument is required.\n", .{});
        errline(args, @min(file_index + 1, args.len), 0);
        if (opt.clean_exit) exit(0) else exit(1);
    }
    std.mem.sort([]const u8, opt.azDefine, {}, strLessThan);
    const filename: []const u8 = args[file_index];
    var zyt = lemon: {
        errdefer opt.deinit(allocator);
        break :lemon try Zitron.create(allocator);
    };
    defer zyt.destroy(allocator);
    zyt.io = init.io;
    zyt.opt = opt;
    zyt.argv = args;
    zyt.filename = filename;
    zyt.linenosflag = opt.linenos;
    check_filename(filename) catch |err| {
        if (opt.linenos) {
            switch (err) {
                error.FileNameHasNewline => {
                    dprint("Filename has newline, line numbers cannot be printed\n", .{});
                },
                error.FileNameHasTab => {
                    dprint("Filename has tab, line numbers cannot be printed\n", .{});
                },
                error.FileNameNotUtf8 => {
                    dprint("Filename is not valid UTF-8, line numbers cannot be printed\n", .{});
                },
            }
            zyt.errorcnt += 1;
        }
    };
    // TODO: don't need the quoted version of either of these...
    zyt.filename = filename;
    zyt.printPreprocessed = opt.print_pp;
    _ = try Symbol_new("$"); // Why? Answer: creates index 0!
    var pstate = try ParserState.create(allocator, zyt);
    defer pstate.destroy();
    pstate.gp = zyt;
    pstate.filename = filename;

    try Parse(pstate);
    if (zyt.printPreprocessed) exit(0);

    for (impl_safe.impls.values()) |impl| {
        if (impl.rule) |rule| {
            // Code generally lives in the Str_safe, I think it's
            // better policy to keep it there.
            rule.code = try Strsafe(impl.code);
            if (impl.line > 0) {
                rule.line = impl.line;
            }
            rule.noCode = false;
            impl.code = try zyt.allocator.realloc(impl.code, 0);
        } else {
            ErrorMsg(zyt.filename, impl.line, "" ++
                "Orphaned impl named {s}", .{impl.name});
            zyt.errorcnt += 1;
        }
    }

    if (zyt.errorcnt > 0 and !zyt.opt.fifo) {
        logger.err("exiting with {d} error{s}", .{ zyt.errorcnt, if (zyt.errorcnt == 1) "" else "s" });
        // Give hint if errors are outrageous
        if (zyt.errorcnt > 23) {
            logger.err("hint: check the input file, does it say `.zy` (good) or `.zig` (not good)?", .{});
        }
        if (opt.clean_exit) exit(0) else exit(@truncate(zyt.errorcnt));
    }
    if (zyt.nrule == 0) {
        logger.err("Empty grammar.", .{});
        if (opt.clean_exit) exit(0) else exit(1);
    }

    zyt.errsym = Symbol_find("error");

    // Count and index the symbols of the grammar
    _ = try Symbol_new("{default}");
    zyt.symbols = Symbol_arrayof();
    sort(*Symbol, zyt.symbols, {}, Symbol_lessThanFn);
    if (p_symbols) for (zyt.symbols) |symbol| {
        std.debug.print("{s} ", .{symbol.name});
    };
    for (zyt.symbols, 0..) |sym, i| {
        sym.index = @intCast(i);
    }
    {
        var i: u32 = @intCast(zyt.symbols.len);
        while (zyt.symbols[i - 1].type == .multiterminal) : (i -= 1) {}
        dbgassert(strcmp(zyt.symbols[i - 1].name, "{default}"));
        zyt.nsymbol = i - 1;
        i = 1;
        while (isUpper(zyt.symbols[i].name[0])) : (i += 1) {}
        zyt.nterminal = i;
    }
    sequenceRules(zyt);
    if (p_check1 or p_symbols) {
        dprint("Sorted rules: {s}\n", .{zyt.filename});
        var rp: ?*Rule = zyt.rule;
        var i: usize = 0;
        while (rp) |rule| : (rp = rule.next) {
            dprint("~~~ {s} ({d})\n", .{ rule.lhs.name, rule.iRule });
            i += 1;
        }
        dprint("Rule count: {d}\n", .{i});
        dprint("nsymbol {d} nterminal {d}\n", .{ zyt.nsymbol, zyt.nterminal });
        for (zyt.symbols[0..zyt.nsymbol]) |symbol| {
            dprint("{s} ", .{symbol.name});
        }
        dprint("\n", .{});
    }
    // [1726]
    // /* Generate a reprint of the grammar, if requested on the command line */
    if (opt.grammar) {
        try Reprint(zyt);
    } else {
        SetSize(zyt.nterminal + 1);
        // Find the precedence for every production rule (that has one)
        FindRulePrecedences(zyt);
        // Compute the lambda-nonterminals and the first-sets for every
        // nonterminal
        try FindFirstSets(zyt);
        if (p_check1) {
            var rp: ?*Rule = zyt.rule;
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
        dbgassert(zyt.nstate == 0);
        // Compute all LR(0) states.  Also record follow-set propagation
        // links so that the follow-set can be computed later
        try FindStates(zyt);
        zyt.sorted = State_arrayof();
        dbgassert(zyt.sorted.len == zyt.nstate);
        if (p_check1) {
            for (zyt.sorted, 0..) |stp, i| {
                dprint("State {d} #{d}: ", .{ i, stp.statenum });
                if (stp.bp) |bp| {
                    dprint("{s}", .{bp.rp.lhs.name});
                } else {
                    dprint("(null)", .{});
                }
                dprint("\n", .{});
            }
        }
        // /* Tie up loose ends on the propagation links */
        try FindLinks(zyt);
        if (p_check1) {
            for (zyt.sorted) |stp| {
                var maybe_cfp: ?*Config = stp.cfp;
                while (maybe_cfp) |cfp| : (maybe_cfp = cfp.next) {
                    dprint("cfp: {s}:{d} fplp count: ", .{ cfp.rp.lhs.name, cfp.rp.index });
                    var plp_count: usize = 0;
                    var maybe_plp: ?*PLink = cfp.fplp;
                    while (maybe_plp) |plp| : (maybe_plp = plp.next) {
                        plp_count += 1;
                    }
                    dprint("{d}\n", .{plp_count});
                }
            }
        }
        // Compute the follow set of every reducible configuration
        FindFollowSets(zyt);

        // Compute the action tables
        try FindActions(zyt);
        // Compress the action tables
        if (!opt.no_compress) try CompressTables(zyt);
        if (p_check1) {
            for (zyt.sorted[0..zyt.nstate]) |stp| {
                dprint("State {d}:", .{stp.statenum});
                var m_ap: ?*Action = stp.ap;
                while (m_ap) |ap| : (m_ap = ap.next) {
                    dprint(" {s}", .{ap.sp.name});
                }
                dprint("\n", .{});
            }
        }
        // Reorder and renumber the states so that states with fewer choices
        // occur at the end.  This is an optimization that helps make the
        // generated parser tables smaller.
        if (!opt.no_resort) ResortStates(zyt);
        // Generate a report of the parser generated.  (the "y.output" file)
        if (!opt.quiet) try ReportOutput(zyt);
        // Generate the source code for the parser.
        try ReportTable(zyt);
        // Produce a separate enum file when requested.
        if (opt.enum_file) try ReportHeader(zyt);
    }
    if (opt.statistics) {
        var stdout_writer = std.Io.File.stdout().writer(zyt.io, &stdout_buffer);
        const out = &stdout_writer.interface;
        try out.writeAll("Parser statistics:\n");
        try stats_line(out, "terminal symbols", zyt.nterminal);
        try stats_line(out, "non-terminal symbols", zyt.nsymbol - zyt.nterminal);
        try stats_line(out, "total symbols", zyt.nsymbol);
        try stats_line(out, "rules", zyt.nrule);
        try stats_line(out, "states", zyt.nxstate);
        try stats_line(out, "conflicts", zyt.nconflict);
        try stats_line(out, "action table entries", zyt.nactiontab);
        try stats_line(out, "lookahead table entries", zyt.nlookaheadtab);
        try stats_line(out, "total table size (bytes)", zyt.tablesize);
        try out.flush();
    }
    if (zyt.nconflict > 0) {
        dprint("{d} parsing conflicts.\n", .{zyt.nconflict});
    }
    // return 0 on success, 1 on failure.
    if (zyt.errorcnt > 0 or zyt.nconflict > 0) {
        if (opt.clean_exit) exit(0) else exit(1);
    }
    std.process.cleanExit(init.io);
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
            var before: usize = 0;
            if (is_debug) {
                while (maybe_list) |list| : (maybe_list = @field(list, next)) {
                    before += 1;
                }
                maybe_list = a;
            }
            while (maybe_list) |list| {
                ep = list;
                maybe_list = @field(list, next);
                @field(ep.?, next) = null;
                var i: usize = 0;
                while (i < LISTSIZE - 1 and set[i] != null) : (i += 1) {
                    ep = merge(set[i], ep);
                    set[i] = null;
                }
                set[i] = merge(set[i], ep);
            }

            ep = null;
            for (0..LISTSIZE) |i| {
                if (set[i]) |tail| {
                    ep = merge(tail, ep);
                }
            }
            var after: usize = 0;
            if (is_debug) {
                var maybe_ep = ep;
                while (maybe_ep) |list| : (maybe_ep = @field(list, next)) {
                    after += 1;
                }
                if (before != after) {
                    std.debug.panic("list: before {d}, after {d}", .{ before, after });
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
            while (a != null and b != null) {
                const a_ptr = a.?;
                const b_ptr = b.?;
                if (lteFn(a_ptr, b_ptr)) {
                    @field(ptr, next) = a_ptr;
                    ptr = a_ptr;
                    a = @field(a_ptr, next);
                } else {
                    @field(ptr, next) = b_ptr;
                    ptr = b_ptr;
                    b = @field(b_ptr, next);
                }
            }
            if (a) |a_ptr| {
                @field(ptr, next) = a_ptr;
            } else {
                @field(ptr, next) = b;
            }
            return head;
        }
    }.msort;
}

fn sequenceRules(zyt: *Zitron) void {
    // Assign sequential rule numbers.  Start with 0.  Put rules that have no
    // reduce action C-code associated with them last, so that the switch()
    // statement that selects reduction actions will have a smaller jump table.
    // NOTE: the original code does all this assigning, then sorts. I don't
    // see why, since we create the order right here.  We can just:
    var rnum: u32 = 0;
    var rp: ?*Rule = zyt.rule;
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
    zyt.nruleWithAction = rnum;
    rp = no_act_head; // This works correctly even if there are no no-action rules
    while (rp) |rule| : (rp = rule.next) {
        dbgassert(rule.code.len == 0);
        rule.iRule = rnum;
        rnum += 1;
    }
    zyt.startRule = zyt.rule;
    // We must have at least one rule, or we bailed already, so this works too:
    zyt.rule = if (action_head) |act_head| act_head else no_act_head.?;
    if (action_head) |_| {
        // Means we have an action_tail too.  Not necessarily a no_act_head,
        // but this is fine:
        action_tail.?.next = no_act_head;
    } // Sorted!
    rp = zyt.startRule;
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
    dbgassert(!is_a_strsafe);
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
    const symbol = try symbol_map.intern(str);
    symbol.useCnt += 1;
    return symbol;
}

fn Symbol_count() usize {
    return symbol_map.safe.count();
}

fn Symbol_find(str: []const u8) ?*Symbol {
    dbgassert(is_symbol_map);
    return symbol_map.safe.get(str);
}

// NOTE: This is sorted after fetching, which invalidates the
// use of Symbol_find.
fn Symbol_arrayof() []*Symbol {
    dbgassert(is_symbol_map);
    return symbol_map.safe.values();
}

//| [5840]
/// Compare two symbols for sorting purposes.  Return negative,
/// zero, or positive if a is less then, equal to, or greater
/// than b.
///
/// Symbols that begin with upper case letters (terminals or tokens)
/// must sort before symbols that begin with lower case letters
/// (non-terminals).  And MULTITERMINAL symbols (created using the
/// %token_class directive) must sort at the very end. Other than
/// that, the order does not matter.
///
/// We find experimentally that leaving the symbols in their original
/// order (the order they appeared in the grammar file) gives the
/// smallest parser tables in SQLite.
fn Symbol_lessThanFn(_: void, a: *Symbol, b: *Symbol) bool {
    const a_val: u8 = if (a.type == .multiterminal) 3 else if (a.name[0] > 'Z') 2 else 1;
    const b_val: u8 = if (b.type == .multiterminal) 3 else if (b.name[0] > 'Z') 2 else 1;
    if (a_val < b_val) return true else if (a_val > b_val) return false;
    return (a.index > b.index);
}

//| [1300] configlist.c
//|
//| This is one of the places where the Lemon generator uses 'static' global
//| state.  No sin in that, not in an application, but we're going to package it
//| up into:

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

fn Configlist_deinit() void {
    dbgassert(is_a_configlists);
    defer is_a_configlists = false;
    cf_ls.config_table.clearAndFree(cf_ls.allocator);
    cf_ls.pool.deinit();
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
    if (p_check1) {
        dprint("[{d},{d}] ", .{ rp.index, dot });
    }
    const maybe_cfp = cf_ls.config_table.getKey(&model);
    if (p_check1) {
        if (maybe_cfp) |_| {
            dprint("+ ", .{});
        } else {
            dprint(". ", .{});
        }
    }
    if (maybe_cfp) |cfp| {
        return cfp;
    }
    var cfp = try newconfig();
    cfp.rp = rp;
    cfp.dot = dot;
    cfp.fws = try cf_ls.allocator.alloc(bool, set_size);
    @memset(cfp.fws, false);
    dbgassert(cfp.stp == null);
    dbgassert(cfp.next == null);
    dbgassert(cfp.fplp == null);
    dbgassert(cfp.bplp == null);
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
    dbgassert(cfp.stp == null);
    dbgassert(cfp.next == null);
    dbgassert(cfp.fplp == null);
    dbgassert(cfp.bplp == null);
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
fn Configlist_closure(zyt: *Zitron) !void {
    var this_cfp: ?*Config = cf_ls.current;
    var scan_count: usize = 0;
    scan: while (this_cfp) |cfp| : (this_cfp = cfp.next) {
        scan_count += 1;
        const rp = cfp.rp;
        const dot = cfp.dot;
        if (p_check1) {
            dprint("Closure: {s} #{d}\n", .{ rp.lhs.name, dot });
        }
        if (dot >= rp.rhs.len) continue :scan;
        const sp = rp.rhs[dot];
        if (sp.type == .nonterminal) {
            if (sp.rule == null and sp != zyt.errsym) {
                ErrorMsg(zyt.filename, 0, "" ++
                    "Nonterminal \"{s}\" has no rules.", .{sp.name});
                zyt.errorcnt += 1;
            }
            var this_newrp = sp.rule;
            while (this_newrp) |newrp| : (this_newrp = newrp.nextlhs) {
                if (p_check1) {
                    dprint("    lhs {s}:{d} ", .{ newrp.lhs.name, newrp.index });
                }
                const newcfp = try Configlist_add(newrp, 0);
                var i: usize = dot + 1;
                dots: while (i < rp.rhs.len) : (i += 1) {
                    const xsp = rp.rhs[i];
                    if (p_check1) {
                        dprint("{s}, ", .{xsp.name});
                    }
                    // TODO: refactor this:
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
                }
                if (i == rp.rhs.len) try Plink_add(&cfp.fplp, newcfp);
                if (p_check1) {
                    dprint("\n", .{});
                }
            }
        }
    }
    if (p_check1) {
        dprint("    count {d}\n", .{scan_count});
    }
}

const Configlist_msort = mergeSortFn(Config, "next", Configcmp);

fn Configlist_sort() void {
    cf_ls.current = if (cf_ls.current) |cfp| Configlist_msort(cfp) else null;
    cf_ls.currentend = &cf_ls.current;
}

const Configlist_msortBasis = mergeSortFn(Config, "bp", Configcmp);

fn Configlist_sortbasis() void {
    cf_ls.basis = if (cf_ls.basis) |bp| Configlist_msortBasis(bp) else null;
    cf_ls.basisend = &cf_ls.basis;
}
/// Return a pointer to the head of the configuration list
/// and reset the list.
fn Configlist_return() ?*Config {
    const old = cf_ls.current;
    cf_ls.current = null;
    cf_ls.currentend.* = cf_ls.current;
    return old;
}

/// Return a pointer to the head of the configuration basis list
/// and reset the list.
fn Configlist_basis() *Config {
    const old = cf_ls.basis;
    cf_ls.basis = null;
    cf_ls.basisend.* = cf_ls.basis;
    return old.?;
}

/// Free all elements of the given configuration list.
fn Configlist_eat(cfp: ?*Config, allocator: Allocator) void {
    var nextcfp: ?*Config = cfp;
    while (nextcfp) |this_cfp| {
        nextcfp = this_cfp.next;
        dbgassert(this_cfp.fplp == null);
        dbgassert(this_cfp.bplp == null);
        if (this_cfp.fws.len > 0) allocator.free(this_cfp.fws);
        deleteconfig(this_cfp);
    }
}

/// Free all sets in a Configuration list
fn Configlist_freesets(cfp: ?*Config, allocator: Allocator) void {
    var nextcfp: ?*Config = cfp;
    while (nextcfp) |this_cfp| {
        nextcfp = this_cfp.next;
        if (this_cfp.fws.len > 0) allocator.free(this_cfp.fws);
        this_cfp.fws.len = 0;
    }
}

test "exe mentioned" {
    try std.testing.expect(true);
}

test "fifo option fixes dependent file outputs" {
    var args = [_][:0]const u8{ "zitron", "--fifo", "-Se", "grammar.zy" };
    var opt: Options = .{};
    defer opt.deinit(std.testing.allocator);

    const file_index = try optionsInit(&opt, &args, std.testing.allocator);

    try std.testing.expectEqual(@as(usize, 3), file_index);
    try std.testing.expect(opt.fifo);
    try std.testing.expect(!opt.sql_flag);
    try std.testing.expect(!opt.enum_file);
    try std.testing.expect(opt.quiet);
}

test "unbundle option parses as short and long flag" {
    {
        var args = [_][:0]const u8{ "zitron", "-u", "grammar.zy" };
        var opt: Options = .{};
        defer opt.deinit(std.testing.allocator);

        const file_index = try optionsInit(&opt, &args, std.testing.allocator);

        try std.testing.expectEqual(@as(usize, 2), file_index);
        try std.testing.expectEqual(!config.unbundle, opt.unbundle);
    }
    {
        var args = [_][:0]const u8{ "zitron", "--unbundle", "grammar.zy" };
        var opt: Options = .{};
        defer opt.deinit(std.testing.allocator);

        const file_index = try optionsInit(&opt, &args, std.testing.allocator);

        try std.testing.expectEqual(@as(usize, 2), file_index);
        try std.testing.expectEqual(!config.unbundle, opt.unbundle);
    }
}

test "preprocessor keeps nested else inside an excluded branch excluded" {
    var args = [_][:0]const u8{ "zitron", "grammar.zy" };
    var opt: Options = .{};
    defer opt.deinit(std.testing.allocator);
    _ = try optionsInit(&opt, &args, std.testing.allocator);

    const input = try std.testing.allocator.dupeZ(u8,
        \\%ifdef OUTER
        \\outer
        \\%ifdef INNER
        \\inner
        \\%else
        \\inner else
        \\%endif
        \\end outer
        \\%else
        \\outer else
        \\%endif
        \\visible
        \\
    );
    defer std.testing.allocator.free(input);

    var errcnt: usize = 0;
    preprocess_input(&opt, &errcnt, input);

    try std.testing.expectEqual(@as(usize, 0), errcnt);
    try std.testing.expect(mem.indexOf(u8, input, "\nouter\n") == null);
    try std.testing.expect(mem.indexOf(u8, input, "inner else") == null);
    try std.testing.expect(mem.indexOf(u8, input, "end outer") == null);
    try std.testing.expect(mem.indexOf(u8, input, "outer else") != null);
    try std.testing.expect(mem.indexOf(u8, input, "visible") != null);
}

test "sql string literals escape quotes" {
    var buf: AllocatingWriter = .init(std.testing.allocator);
    defer buf.deinit();

    try writeSqlString(&buf.writer, "can't stop");

    const got = try buf.toOwnedSlice();
    defer std.testing.allocator.free(got);
    try std.testing.expectEqualStrings("'can''t stop'", got);
}

test "impl signatures include aliases without code" {
    var rhs = [_][]const u8{ "left", "", "right" };
    var impl = Impl.empty;
    impl.name = "@expr_mix";
    impl.lhsalias = "out";
    impl.rhsalias = &rhs;

    var buf: AllocatingWriter = .init(std.testing.allocator);
    defer buf.deinit();

    try writeImplSignature(&buf.writer, &impl);

    const got = try buf.toOwnedSlice();
    defer std.testing.allocator.free(got);
    try std.testing.expectEqualStrings("@expr_mix(out; left, , right)", got);
}

test "impl signatures ignore an aligned but entirely blank RHS alias slice" {
    var rhs = [_][]const u8{ "", "", "" };
    var impl = Impl.empty;
    impl.name = "@uncaptured";
    impl.rhsalias = &rhs;

    var buf: AllocatingWriter = .init(std.testing.allocator);
    defer buf.deinit();

    try writeImplSignature(&buf.writer, &impl);

    const got = try buf.toOwnedSlice();
    defer std.testing.allocator.free(got);
    try std.testing.expectEqualStrings("@uncaptured()", got);
}

test "rule alias detection ignores uncaptured RHS slots" {
    var uncaptured = [_][]const u8{ "", "" };
    var rule = Rule.empty;
    rule.lhsalias = "";
    rule.rhsalias = &uncaptured;
    try std.testing.expect(!ruleHasAliases(&rule));

    rule.rhsalias[1] = "value";
    try std.testing.expect(ruleHasAliases(&rule));
}

test "destructor emission treats blank RHS aliases as aligned slots" {
    Strsafe_init(std.testing.allocator);
    defer Strsafe_free();

    var token = Symbol.empty;
    token.type = .terminal;
    token.index = 7;
    var lhs = Symbol.empty;
    var rhs = [_]*Symbol{ &token, &token };
    var aliases = [_][]const u8{ "", "" };
    var rule = Rule.empty;
    rule.lhs = &lhs;
    rule.rhs = &rhs;
    rule.rhsalias = &aliases;
    rule.codePrefix = try std.testing.allocator.alloc(u8, 0);

    var token_destructor = "_ = $$;".*;
    var zyt = Zitron.empty;
    zyt.allocator = std.testing.allocator;
    zyt.tokendest = &token_destructor;

    try std.testing.expect(!try translate_code(&zyt, &rule));
    try std.testing.expectEqual(@as(usize, 2), mem.count(u8, rule.codePrefix, "yy_destructor"));
}

test "named RHS alias search finds captures after blank slots" {
    const aliases = [_][]const u8{ "first", "", "last", "" };
    try std.testing.expectEqual(@as(?usize, 2), nextNamedAliasIndex(&aliases, 1));
    try std.testing.expectEqual(@as(?usize, null), nextNamedAliasIndex(&aliases, 3));
}

test "compact impl aliases compare by name against aligned rule slots" {
    const rule_aliases = [_][]const u8{ "first", "", "last" };
    const matching = [_][]const u8{ "first", "last" };
    try std.testing.expect(compareRhsAliasNames(&matching, &rule_aliases) == .match);

    const missing = compareRhsAliasNames(&.{"first"}, &rule_aliases);
    try std.testing.expect(missing == .missing_rule);
    try std.testing.expectEqualStrings("last", missing.missing_rule);

    const extra = [_][]const u8{ "first", "last", "extra" };
    try std.testing.expect(compareRhsAliasNames(&extra, &rule_aliases) == .extra_impl);

    const differing = compareRhsAliasNames(&.{ "first", "other" }, &rule_aliases);
    try std.testing.expect(differing == .differing);
    try std.testing.expectEqualStrings("other", differing.differing.impl_alias);
    try std.testing.expectEqualStrings("last", differing.differing.rule_alias);
}

test "define sorting comparator is lexicographic for equal-length names" {
    try std.testing.expect(strLessThan({}, "ab", "ba"));
    try std.testing.expect(!strLessThan({}, "ba", "ab"));
    try std.testing.expect(!strLessThan({}, "ab", "ab"));
}
