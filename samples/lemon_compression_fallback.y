%name Parse
%token_type {int}
%extra_argument {int *result}
%include {
#include <assert.h>
#include <stdlib.h>
}
%syntax_error { if (*result == 0) *result = -1; }
%parse_accept { if (*result == 0) *result = 1; }
%fallback ID D.

start ::= PSTART n D.
start ::= QSTART n E.
n ::= a.
n ::= x.
a ::= C.
x ::= C ID.

%code {
static int run(int prefix, int middle, int suffix){
  int result = 0;
  void *parser = ParseAlloc(malloc);
  assert(parser != 0);
  Parse(parser, prefix, 0, &result);
  Parse(parser, middle, 0, &result);
  Parse(parser, suffix, 0, &result);
  Parse(parser, 0, 0, &result);
  ParseFree(parser, free);
  return result;
}

int main(void){
  return run(PSTART, C, D) != 1 || run(QSTART, C, D) != -1;
}
}
