# Zitron


Zitron[^1] is an [LALR(1)][lalr] parser generator, closely based on
[Lemon][lem], the parser generator D. Richard Hipp wrote for SQLite.
It has been adopted and modified to produce Zig code.

So closely is Zitron based on Lemon, in fact, that it includes
a full port of Lemon, which has been tested and produces byte-for-byte
identical output for numerous Lemon grammars, including that of SQLite
itself.  While I can think of no actual advantage to using `lemon.zig`
rather than `lemon.c`, translating the former was an essential step
in writing the latter, and I saw no reason to leave it stranded in the
commit history.  Let it serve as an artifact showing the fidelity with
which this translation was prepared.  Any bugs in Zitron are almost sure
to be of my own doing, and, with decent confidence, transpired after the
translation of `lemon.zig`.

[lalr]: https://en.wikipedia.org/wiki/LALR_parser
[lem]: https://sqlite.org/lemon.html


## Using Zitron

As [Yet Another Yet Another Compiler-Compiler][yacc][^2], Zitron is
a complete DSL for declaring a parser, and actions to go along with
recognition.  A [detailed manual] is included, itself adopted from
[the original][og].

The manual includes instructions on [integrating with build.zig],
which is a good place to start if you already know your way around
YACC-alikes.  [The manual][detailed manual] is quite comprehensive,
and you really want to read it.

A tokenizer will be necessary.  If you're reading this[^3], a companion
lexer generator does not exist.  It's certainly tractable to roll your
own by hand.  It may also interest you to know that [re2c][re2c] is
able to generate Zig code, although not, at the time of writing, using
labeled switch continue format.

[yacc]: https://en.wikipedia.org/wiki/Yacc
[detailed manual]: /doc/zitron.md
[og]: https://sqlite.org/src/doc/trunk/doc/lemon.html
[integrating with build.zig]: /doc/zitron.md#build
[re2c]: https://re2c.org/manual/manual_zig.html


### Accessories

Zitron has a [tree-sitter], for that colorful syntax we all like, and
textobjects navigation, which at least some of us like as well.

There is also a language server, [zitron-ls], which provides language
services for both the grammar dialect and any embedded Zig code.

These will both work better with a [custom Zig tree-sitter], which has
been extensively reworked to provide accurate syntax categories for
fragments of function code, as well as various improvements in parsing
the container context as well.  It parses every Zig file in the ziglang
repo without any `ERROR` or `MISSING` productions.  `zitron-ls` provides
semantic highlighting for Zig code, so this may be less important if you
use it, which I recommend.

[custom Zig tree-sitter]: https://github.com/mnemnion/tree-sitter-zig

[zitron-ls]: https://github.com/mnmemnion/zitron-ls

[tree-sitter]: https://github.com/mnmemnion/tree-sitter-zitron


### Licensing

Lemon is in the public domain.  Whether a close technical translation
is even entitled to a separate copyright is somewhat unclear; for the
avoidance of doubt, `lemon.zig` is also dedicated to the public domain.

Zitron itself is licensed `BSD 0`, which is morally equivalent, and
compatible with more international licensing régimes.

Some of the Lemon grammars in the `samples/` directory have their own
licenses, which you will find in `samples/licenses/`.


## Future Work

This project has the great advantage of standing upon the shoulders of a
giant.  Lemon parsers run on every smartphone, the great majority of PCs
and servers, Naval vessels, embedded systems, and much else; the design
has proven its merit a myriad times over.

And yet I have the temerity to contemplate some changes, to improve the
developer experience, even perhaps the user experience, of writing and
running Zitron grammars (respectively).  Some of those changes already
exist!

It's too early to guarantee that every Zitron grammar written today will
be forward-compatible with every Zitron release, down to the last build
flag.  Decent chance it will be, though.  If you find yourself relying
on Zitron in a project, I would be most pleased to hear about it, and
will keep that in consideration in the event of any breaking change.

Most of what I'm contemplating is strictly additive, in any case.  No
promises, no warranty, as the Lemon manual puts it:

> If it breaks, you get to keep both pieces.

[^1]: The name Zitron is a sort of pan-European compromise between
  several spellings of "citron", a word which refers to a different
  citrus entirely in English, but to the lemon in those European
  languages where it doesn't sound like 'lemon'.  This artifice,
  much like the EU, is guaranteed to please no one.

[^2]: Which I suppose makes me yet another yet another compiler-compiler
  compiler.  Hazard of the trade!  Quite the yacc shave, I must admit.

[^3]: Safe bet
