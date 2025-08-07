//! *************************************************************************
//! Driver template for the Zitron parser generator.
//!
//! The "zitron" program processes an LALR(1) input grammar file, then uses
//! this template to construct a parser.  The "zitron" program inserts text at
//! each "%%" line.  Any occurance of the lemon emoji is used to interpolate
//! values from the generator, in lieu of macros.  Otherwise, the content of
//! this template is copied straight through into the generate parser source
//! file.
//!
//! The following is the concatenation of all %include directives from the
//! input grammar file:
//!
// ************ Begin %include sections from the grammar ************************
%%
// **************** End of %include directives **********************************
//  This specifies the token enum.  If generated separately this is an import of
//  that file.
// ***************** Begin token definitions *************************************
%%
// **************** End token definitions ***************************************
// The next sections is a series of constant definitions dictating
// various aspects of the generated parser.
//
//    YYCODETYPE         is the data type used to store the integer codes
//                       that represent terminal and non-terminal symbols.
//                       "unsigned char" is used if there are fewer than
//                       256 symbols.  Larger types otherwise.
//    YYNOCODE           is a number of type YYCODETYPE that is not used for
//                       any terminal or nonterminal symbol.
//    YYFALLBACK         If defined, this indicates that one or more tokens
//                       (also known as: "terminal symbols") have fall-back
//                       values which should be used if the original symbol
//                       would not parse.  This permits keywords to sometimes
//                       be used as identifiers, for example.
//    YYACTIONTYPE       is the data type used for "action codes" - numbers
//                       that indicate what to do in response to the next
//                       token.
//    ParseTOKENTYPE     is the data type used for minor type for terminal
//                       symbols.  Background: A "minor type" is a semantic
//                       value associated with a terminal or non-terminal
//                       symbols.  For example, for an "ID" terminal symbol,
//                       the minor type might be the name of the identifier.
//                       Each non-terminal can have a different minor type.
//                       Terminal symbols all have the same minor type, though.
//                       This macros defines the minor type for terminal
//                       symbols.
//    YYMINORTYPE        is the data type used for all minor types.
//                       This is typically a union of many types, one of
//                       which is ParseTOKENTYPE.  The entry in the union
//                       for terminal symbols is called "yy0".
//    YYSTACKDEPTH       is the maximum depth of the parser's stack.  If
//                       zero the stack is dynamically sized using realloc()
//    ParseARG_SDECL     A static variable declaration for the %extra_argument
//    ParseARG_PDECL     A parameter declaration for the %extra_argument
//    ParseARG_PARAM     Code to pass %extra_argument as a subroutine parameter
//    ParseARG_STORE     Code to store %extra_argument into yypParser
//    ParseARG_FETCH     Code to extract %extra_argument from yypParser
//    ParseCTX_*         As ParseARG_ except for %extra_context
//    YYREALLOC          Name of the realloc() function to use
//    YYFREE             Name of the free() function to use
//    YYDYNSTACK         True if stack space should be extended on heap
//    YYERRORSYMBOL      is the code number of the error symbol.  If not
//                       defined, then do no error processing.
//    YYNSTATE           the combined number of states.
//    YYNRULE            the number of rules in the grammar
//    YYNTOKEN           Number of terminal symbols
//    YY_MAX_SHIFT       Maximum value for shift actions
//    YY_MIN_SHIFTREDUCE Minimum value for shift-reduce actions
//    YY_MAX_SHIFTREDUCE Maximum value for shift-reduce actions
//    YY_ERROR_ACTION    The yy_action[] code for syntax error
//    YY_ACCEPT_ACTION   The yy_action[] code for accept
//    YY_NO_ACTION       The yy_action[] code for no-op
//    YY_MIN_REDUCE      Minimum value for reduce actions
//    YY_MAX_REDUCE      Maximum value for reduce actions
//    YY_MIN_DSTRCTR     Minimum symbol value that has a destructor
//    YY_MAX_DSTRCTR     Maximum symbol value that has a destructor
//
// ************* Begin constants *****************************************
%%
// ************* End constants *******************************************
// Next are the tables used to determine what action to take based on the
// current state and lookahead token.  These tables are used to implement
// functions that take a state number and lookahead value and return an
// action integer.
//
// Suppose the action integer is N.  Then the action is determined as
// follows
//
//   0 <= N <= YY_MAX_SHIFT             Shift N.  That is, push the lookahead
//                                      token onto the stack and goto state N.
//
//   N between YY_MIN_SHIFTREDUCE       Shift to an arbitrary state then
//     and YY_MAX_SHIFTREDUCE           reduce by rule N-YY_MIN_SHIFTREDUCE.
//
//   N == YY_ERROR_ACTION               A syntax error has occurred.
//
//   N == YY_ACCEPT_ACTION              The parser accepts its input.
//
//   N == YY_NO_ACTION                  No such action.  Denotes unused
//                                      slots in the yy_action[] table.
//
//   N between YY_MIN_REDUCE            Reduce by rule N-YY_MIN_REDUCE
//     and YY_MAX_REDUCE
//
// The action table is constructed as a single large table named yy_action[].
// Given state S and lookahead X, the action is computed as either:
//
//    (A)   N = yy_action[ yy_shift_ofst[S] + X ]
//    (B)   N = yy_default[S]
//
// The (A) formula is preferred.  The B formula is used instead if
// yy_lookahead[yy_shift_ofst[S]+X] is not equal to X.
//
// The formulas above are for computing the action when the lookahead is
// a terminal symbol.  If the lookahead is a non-terminal (as occurs after
// a reduce action) then the yy_reduce_ofst[] array is used in place of
// the yy_shift_ofst[] array.
//
// The following are the tables generated in this section:
//
//  yy_action[]        A single table containing all actions.
//  yy_lookahead[]     A table containing the lookahead for each entry in
//                     yy_action.  Used to detect hash collisions.
//  yy_shift_ofst[]    For each state, the offset into yy_action for
//                     shifting terminals.
//  yy_reduce_ofst[]   For each state, the offset into yy_action for
//                     shifting non-terminals after a reduce.
//  yy_default[]       Default action for each state.
//
// *********** Begin parsing tables **********************************************/
%%
// /********** End of lemon-generated parsing tables *****************************/
//
// The next table maps tokens (terminal symbols) into fallback tokens.
// If a construct like the following:
//
//      %fallback ID X Y Z.
//
// appears in the grammar, then ID becomes a fallback token for X, Y,
// and Z.  Whenever one of the tokens X, Y, or Z is input to the parser
// but it does not parse, the type of the token is changed to ID and
// the parse is retried before an error is thrown.
//
// This feature can be used, for example, to cause some keywords in a language
// to revert to identifiers if they keyword does not apply in the context where
// it appears.
//
const yyFallback = [_]YYCODETYPE{
%%
};
//
/// The following structure represents a single element of the
/// parser's stack.  Information stored includes:
///
///   +  The state number for the parser at this level of the stack.
///
///   +  The value of the token stored at this level of the stack.
///      (In other words, the "major" token.)
///
///   +  The semantic value stored at this level of the stack.  This is
///      the information used by the action routines in the grammar.
///      It is sometimes called the "minor" token.
///
/// After the "shift" half of a SHIFTREDUCE action, the stateno field
/// actually contains the reduce action for the second half of the
/// SHIFTREDUCE.
const yyStackEntry = struct {
    /// The state-number, or reduce action in SHIFTREDUCE.
    stateno: YYACTIONTYPE,
    /// The major token value.  This is the code number for the token at this stack level.
    major: YYCODETYPE,
    /// The user-supplied minor token value.  This is the value of the token.
    minor: YYMINORTYPE,
};
//
/// The state of the parser is completely contained in an instance of
/// the following structure.
pub const yyParser = struct {
    /// Pointer to top element of the stack
    yytos: [*]yyStackEntry,
    //
    // TODO: reckon with `yyhym`
    //
    /// Shifts left before out of the error
    yyerrcnt: usize,
    🍋ARG_SDECL
    🍋CTX_SDECL
    yystackEnd: [*]yyStackEntry,
    yystack: [*]yyStackEntry,
    yystk0: []yyStackEntry,
};
