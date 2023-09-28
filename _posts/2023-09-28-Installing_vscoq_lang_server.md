---
layout: post
title: Installing the VsCoq2 Language Server
usemathjax: true
---

## Install Ocaml

- Install OCaml

## Create an Opam switch for Coq

1. Check version of installed OCaml:

    ```
    $ ocaml --version
    The OCaml toplevel, version 5.1.0
    ```

2. Create the switch:

    ```
    $ opam switch create with-coq 5.1.0
    ```

    Note that the switch name `with-coq` and the succeeding OCaml version may change.

3. Restart shell or run `eval $(opam env)`

4. (Optional). Update opam repo and identify version of Coq available in the repo.
    ```
    $ opam update
    ...
    $ opam list coq
    ...
    coq.8.17.0       --          The Coq Proof Assistant
    coq.8.17.1       --          The Coq Proof Assistant
    coq.8.18.0       --          The Coq Proof Assistant
    ```

4. Pin Coq

    ```
    $ opam pin add coq 8.18.0
    ```

5. Decide to whether to install from the opam repo or from a source repository.

### Option 1. Installing from `opam.ocaml.org`, recommended

1. Install the package:

    ```
    opam update
    opam install vscoq-language-server
    ```

### Option 2. Installing from source

1. Clone the repo:

    ```
    $ git clone https://github.com/coq-community/vscoq --single-branch
    ```

2. Pin from directory:

    ```
    $ opam pin add language-server/
    ```

### Identify the vscoqtop path

1. Identify path to `.opam/`. It's normally `~/.opam`, but you can check with:

    ```
    $ opam config list
    <><> Global opam variables ><><>
    ...
    root              /Users/dashadower/.opam # The current opam root directory
    ...
    ```

2. The vscoqtop binaries are in the path `./opam/YOUR_SWITCH_NAME/bin`.

3. Open VSCode preferences, search for vscoq, and fill in `path to vscoqtop`

### When vscoq bugs out

1. Open command pallete with F1.
2. search for `Developer: reload window`. It should reload the extension which should sort most problems.