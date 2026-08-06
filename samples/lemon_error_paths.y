%include {
#include <assert.h>
#include <stddef.h>
#include <stdlib.h>

typedef struct Token {
  size_t id;
} Token;

typedef struct Stats {
  size_t syntax_errors;
  size_t parse_failures;
  size_t accepts;
  size_t stack_overflows;
  size_t last_error;
  size_t exact_matches;
  size_t wildcard_matches;
  size_t destroyed[16];
} Stats;

%ifdef NO_RECOVERY
#define YYNOERRORRECOVERY 1
%endif
}

%name Parser
%extra_context {Stats *stats}
%token_type {Token}
%stack_size 4

%left BAD OTHER.
%wildcard WILD.

%token_destructor {
  stats->destroyed[$$.id]++;
}

%syntax_error {
  stats->syntax_errors++;
  if (yymajor != 0) stats->last_error = yyminor.id;
}

%parse_failure {
  stats->parse_failures++;
}

%parse_accept {
  stats->accepts++;
}

%stack_overflow {
  stats->stack_overflows++;
}

input ::= A B.
input ::= chain B.
input ::= WILD_START wildcard_value B.
chain ::= .
chain ::= C chain.
wildcard_value ::= EXACT. {
  stats->exact_matches++;
}
wildcard_value ::= WILD. {
  stats->wildcard_matches++;
}
%ifdef ERROR_SYMBOL
input ::= A error B.
%endif

%code {
static Token token(size_t id) {
  Token result = { id };
  return result;
}

static void test_valid_input(void) {
  Stats stats = {0};
  void *parser = ParserAlloc(malloc, &stats);
  assert(parser != NULL);

  Parser(parser, A, token(1));
  Parser(parser, B, token(2));
  Parser(parser, 0, token(0));

  assert(stats.syntax_errors == 0);
  assert(stats.parse_failures == 0);
  assert(stats.accepts == 1);
  assert(stats.destroyed[1] == 1);
  assert(stats.destroyed[2] == 1);

  ParserFree(parser, free);
}

static void test_wildcard_lookup(void) {
  Stats stats = {0};
  void *parser = ParserAlloc(malloc, &stats);
  size_t id;
  assert(parser != NULL);

  Parser(parser, WILD_START, token(9));
  Parser(parser, EXACT, token(10));
  Parser(parser, B, token(11));
  Parser(parser, 0, token(0));

  assert(stats.exact_matches == 1);
  assert(stats.wildcard_matches == 0);
  ParserFree(parser, free);

  parser = ParserAlloc(malloc, &stats);
  assert(parser != NULL);
  Parser(parser, WILD_START, token(12));
  Parser(parser, OTHER, token(13));
  Parser(parser, B, token(14));
  Parser(parser, 0, token(0));

  assert(stats.syntax_errors == 0);
  assert(stats.accepts == 2);
  assert(stats.exact_matches == 1);
  assert(stats.wildcard_matches == 1);
  ParserFree(parser, free);

  for (id = 9; id < 15; id++) assert(stats.destroyed[id] == 1);
}

static void test_incomplete_input(void) {
  Stats stats = {0};
  void *parser = ParserAlloc(malloc, &stats);
  assert(parser != NULL);

  Parser(parser, A, token(1));
  Parser(parser, 0, token(0));

  assert(stats.syntax_errors == 1);
%ifdef NO_RECOVERY
  assert(stats.parse_failures == 0);
%else
  assert(stats.parse_failures == 1);
%endif

  ParserFree(parser, free);
  assert(stats.destroyed[1] == 1);
}

static void test_stack_overflow_ownership(void) {
  Stats stats = {0};
  void *parser = ParserAlloc(malloc, &stats);
  size_t i;
  assert(parser != NULL);

  for (i = 0; i < 4; i++) Parser(parser, C, token(5));

  assert(stats.stack_overflows == 1);
  assert(stats.destroyed[5] == 4);

  Parser(parser, A, token(6));
  Parser(parser, B, token(7));
  Parser(parser, 0, token(0));

  assert(stats.accepts == 1);
  assert(stats.destroyed[6] == 1);
  assert(stats.destroyed[7] == 1);

  ParserFree(parser, free);
}

static void test_empty_reduce_overflow_ownership(void) {
  Stats stats = {0};
  void *parser = ParserAlloc(malloc, &stats);
  size_t i;
  assert(parser != NULL);

  for (i = 0; i < 3; i++) Parser(parser, C, token(5));
  Parser(parser, B, token(8));

  assert(stats.stack_overflows == 1);
  assert(stats.destroyed[5] == 3);
  assert(stats.destroyed[8] == 1);

  Parser(parser, A, token(6));
  Parser(parser, B, token(7));
  Parser(parser, 0, token(0));

  assert(stats.accepts == 1);
  assert(stats.destroyed[6] == 1);
  assert(stats.destroyed[7] == 1);

  ParserFree(parser, free);
}

%ifdef ERROR_SYMBOL
static void test_error_symbol_recovery(void) {
  Stats stats = {0};
  void *parser = ParserAlloc(malloc, &stats);
  size_t id;
  assert(parser != NULL);

  Parser(parser, A, token(1));
  Parser(parser, BAD, token(2));
  Parser(parser, BAD, token(3));
  Parser(parser, B, token(4));
  Parser(parser, 0, token(0));

  assert(stats.syntax_errors == 1);
  assert(stats.last_error == 2);
  assert(stats.parse_failures == 0);
  assert(stats.accepts == 1);
  for (id = 1; id < 5; id++) assert(stats.destroyed[id] == 1);

  ParserFree(parser, free);
}

static void test_unrecoverable_error(void) {
  Stats stats = {0};
  void *parser = ParserAlloc(malloc, &stats);
  assert(parser != NULL);

  Parser(parser, BAD, token(1));

  assert(stats.syntax_errors == 1);
  assert(stats.parse_failures == 1);
  assert(stats.destroyed[1] == 1);

  Parser(parser, A, token(2));
  Parser(parser, B, token(3));
  Parser(parser, 0, token(0));

  assert(stats.accepts == 1);
  ParserFree(parser, free);
}
%else
static void test_discard_recovery(void) {
  Stats stats = {0};
  void *parser = ParserAlloc(malloc, &stats);
  size_t id;
  assert(parser != NULL);

  Parser(parser, A, token(1));
  Parser(parser, BAD, token(2));
  Parser(parser, BAD, token(3));
  Parser(parser, B, token(4));
  Parser(parser, 0, token(0));

%ifdef NO_RECOVERY
  assert(stats.syntax_errors == 2);
%else
  assert(stats.syntax_errors == 1);
%endif
  assert(stats.parse_failures == 0);
  assert(stats.accepts == 1);
  for (id = 1; id < 5; id++) assert(stats.destroyed[id] == 1);

  ParserFree(parser, free);
}
%endif

int main(void) {
  test_valid_input();
  test_wildcard_lookup();
  test_incomplete_input();
  test_stack_overflow_ownership();
  test_empty_reduce_overflow_ownership();
%ifdef ERROR_SYMBOL
  test_error_symbol_recovery();
  test_unrecoverable_error();
%else
  test_discard_recovery();
%endif
  return 0;
}
}
