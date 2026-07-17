# Cnum refactor benchmark

This implementations mirrors the linux kernel implementation of cnum. It's
presence here is intended for showing the improvement on the refactoring of
`contains`, `normalize` and `smin/smax` as of
<https://git.kernel.org/pub/scm/linux/kernel/git/bpf/bpf-next.git/tree/?id=c314bcaa9d5dc34b0c643eac85f675fb8c8bfbaa>.

The current results are in [results.md](./results.md)

Compilation is done through the Makefile. Make sure you have at least `gcc`
installed:

```bash
make
```

You can change the compiler setting the variable `CC`, e.g.:

```bash
make CC=clang
```

Or generate debug symbols and address sanitizing with:

```bash
make DEBUG=1
```

Then you can run the benchmarks with the resulting artifact `cnum.out`.
