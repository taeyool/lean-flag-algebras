# lean-flag-algebras
The goal of this project is to formalize the results of the paper [Flag Algebras](https://people.cs.uchicago.edu/~razborov/files/flag.pdf) by Alexander A. Razborov.


## Building Documents

This project uses [doc-gen4](https://github.com/leanprover/doc-gen4).

Initially, there is a single file [lakefile.toml](docbuild/lakefile.toml) in [docbuild](docbuild) folder.
The document will be built based on this file.

### Initial build

**WARNING**: Building the document may take hours.

```bash
cd docbuild
MATHLIB_NO_CACHE_ON_UPDATE=1 lake update doc-gen4
MATHLIB_NO_CACHE_ON_UPDATE=1 lake build LeanFlagAlgebras:docs
```

### Updating documents

```bash
cd docbuild
MATHLIB_NO_CACHE_ON_UPDATE=1 lake update LeanFlagAlgebras
MATHLIB_NO_CACHE_ON_UPDATE=1 lake build LeanFlagAlgebras:docs
```

### Showing document on a web browser

```bash
cd docbuild/.lake/build/doc
python3 -m http.server
# Now open 'http://127.0.0.1:8000/' on your web browser.
```
