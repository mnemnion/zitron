# Chatbot Disclosure

An LLM was employed during the translation of this work.  It was
consulted on various trivia of the C language, and sometimes shown
buggy functions in the hope that it would spot something obvious.
Occasionally, this even worked.

The translation itself is entirely my doing, with the exception of a
few nearly-mechanical translations of type definitions.  These required
considerable modification; the main benefit was to copy the comments in
the original as doc comments, and ease the drudgery of writing out the
same field names in the same original order.

The derived works (`zitron.zig` and `ztmpl.zig`) are also entirely of
my personal authorship.  This involved a negligible amount of mostly-
fruitless exploration of various esoterica, and no code generation
whatsoever.

The LLM was also engaged to get a head start on various scripts used in
testing the result of the port against the original.  These are included
in the repo, and it is hopefully obvious which files these are.  While
they were heavily modified after generation, the code found therein is
substantially LLM-generated, but is in any case ancillary to the port
itself.  Insofar as I have any right to do so, it's licensed under the
same terms found in `LICENSE.md`.

The legal status of LLM-generated code remains unclear, and there is
vigorous debate as to the ethics of attaching a copyright and license to
works created or largely derived from chatbot output.  I myself do not
have a firm stance on these questions; regardless, the practice is well
on its way to ubiquity, and I suspect that the legal aspect, at least,
will be resolved by fiat, in favor of the conclusion most conducive to
the interests of the powerful.

That said, I see it as appropriate to include brief documentation of
the role such programs have played in this creation, so that others
are appropriately informed, and may make their own decisions about the
nature of the code here found.  I encourage others to do likewise.
