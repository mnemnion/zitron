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

const OptionType = enum {
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
    .@"type": OptionType,
    label: []const u8,
    arg: []u8,
    message: []const u8,
};

//| [203-238] More forward declarations


//| [239] This defines `LEMON_FALSE` and `LEMON_TRUE` as `Boolean`.  That,
//|   we can fairly skip.

//| [241- ]

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
    @"type": SymbolType,
    /// Linked list of rules of this (if an NT)
    rule: ?*Rule,
    /// fallback token in case this token doesn't parse
    fallback: ?*Symbol,
    /// Precedence if defined (-1 otherwise)
    prec: int, // Should be ?u16 probably
    /// Associativity if precedence is defined
    assoc: E_Assoc
    /// First-set for all rules of this symbol
    firstset: []u8, // NOTE: golemon has map[int] bool here
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
    dtnum: int,  // No idea what the above means yet ¯\_(ツ)_/¯
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
    fws: []u8, // Another map[int]bool
    /// Follow-set forward propagation links
    fplp: *PLink,
    /// Follow-set backwards propagation links
    bplp: *PLink,
    /// Pointer to state which contains this
    stp: *State,
    /// used during followset and shift computations
    status: ConfigStatus,
    /// Next configuration in the state
    next: ?*Config,
    /// The next basis configuration
    bp: ?*Config,
};

const E_Action = enum {
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
};

// TODO: We replace the x down there with a tagged union, once we
// figure out which of the E_Action states has a pointer.

/// Every shift or reduce operation is stored as one of the following
const Action = struct {
    /// The look-ahead symbol
    sp: *Symbol,
    /// Determines the union
    @"type": E_Action,
    x:  extern union {
        /// The new state, if a shift
        stp: ?*State,
        /// The rule, if a reduce
        rp ?*Rule,
    },
    /// SHIFTREDUCE optimization to this symbol
    spOpt: *Symbol,
    /// Next action for this state
    next: ?*Action,
    /// Next action with the same hash
    collide: ?*Action,
};

/// Each state of the generated parser's finite state machine
/// is encoded as an instance of the following structure.
const State = struct{
    /// The basis configurations for this state
    pb: *Config,
    /// All configurations in this set
    cfp *Config,
    /// Sequential number for this state
    statenum: int,
    /// List of actions for this state
    ap: *Action,
    /// Number of actions on terminals
    nTknAct: int,
    /// Number of actions on nonterminals
    nNtAct: int,
    /// yy_action[] offset for terminals
    iTnkOfst: int,
    /// yy_action[] offset for nonterminals
    iNtOfst: int,
    /// Default action is to REDUCE by this rule
    iDfltReduce: int,
    /// The default REDUCE rule.
    pDefltReduce: *Rule,
    /// True if this is an auto-reduce state
    autoreduce: bool,
};

// TODO: Obviously some of those offsets are nullable:

const NO_OFFSET: int = -2147483647;

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



















pub fn main() void {
    std.debug.print("lemon for great justice!\n", .{});
    std.process.exit(0);
}

test "exe mentioned" {
    std.debug.print("hello from lemon main\n", .{});
}

