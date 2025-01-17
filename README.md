# Practical Verification of the Reader Monad

This repository presents a verified implementation of the monad Reader and the monad 
transformer ReaderT written in Agda. It can be translated to Haskell using [agda2hs](https://github.com/agda/agda2hs).
This project was part of the course CSE3000 Research Project at TU Delft in 2022.

## Structure

- `demo/Main.hs` - Contains the demo presented in the paper
- `lib/Control/MonadReader/` - Contains translated Haskell code
- `src/Control/MonadReader/MonadTrans.agda` - Contains MonadTrans record type
- `src/Control/MonadReader/Reader.agda` - Contains Reader record type with all its functions
- `src/Control/MonadReader/ReaderT.agda` - Contains ReaderT record type with all its functions
- `src/VerifiedTypeClasses/` - Contains record types of verified typeclasses with proofs
- `src/ProofUtils/ProofFunctions.agda/` - Contains proof functions adapted from lecture notes of 
  TU Delft course CSE3100 Functional Programming

## Prerequisites:

To use this template it is necessary to have cabal, ghc and make installed. If
you don't have these installed you can follow the instructions below, else you
can continue on to [here.](#dependencies)

### For Windows (Using Chocolately):

It is recommended that you install chocolately as a package manager that allows
for installing software by using the built-in terminal in Windows. For the
latest instruction on installing chocolately [click
here](https://chocolatey.org/install#individual) and use the individual
installation method.

To install all prerequisites execute the following commands in your terminal:
```
choco install ghc cabal make
refreshenv
```

Now you can go ahead and install the dependencies.

## Dependencies

This template relies on a custom fork of both [agda2hs] and [Agda].
To build them from source, do the following:

```
git clone https://github.com/flupe/verification-template
cd verification-template
cabal install Agda    # If there are conflicting dependencies for base use the following flag: --allow-newer=base
cabal install agda2hs # If there are conflicting dependencies for base use the following flag: --allow-newer=base
```

Building Agda may take a while.

In order to use the Haskell prelude of `agda2hs` from your Agda code, you also
need to tell Agda where to locate the library.

Clone Jesper's fork of agda2hs:

```
git clone -b erasure-annotations https://github.com/jespercockx/agda2hs
```
### For Unix:

Inside the file `~/.agda/libraries`, add the following line:

```
/your/path/to/agda2hs/agda2hs.agda-lib
```

### For Windows:

First off execute the following command:

```
(test-path -path $home\AppData\Roaming\agda\libraries -pathtype Leaf) ? (echo "File not created, it already exists") : (new-item -path $home\AppData\Roaming\agda\libraries)
```

Either add the following line to `C:\Users\<USER>\AppData\Roaming\agda\libraries` or alternatively when using powershell `$home\AppData\Roaming\agda\libraries`, 

```
</your/path/to/agda2hs/agda2hs.agda-lib>
```

Or run the following command in powershell:

```
add-content $home\AppData\Roaming\agda\libraries "`n</your/path/to/agda2hs/agda2hs.agda-lib>"
```

*You will have to create this file if it does not exist.*

## Development

You should be good to go. Open any file in the `src/` directory inside your IDE of choice and
you should be able to use the Haskell prelude in your code without any issue.

Running `make` at the root of the project will:
- compile `Everything.agda` using `agda2hs`.
  Don't forget to import your agda files in `Everything.agda` to have them
  compile to Haskell automatically.
- compile the Haskell library generated from the Agda files in `lib/`.
- comile the demo Haskell executable in `demo/`

[Agda]:    https://github.com/agda/Agda
[agda2hs]: https://github.com/agda/agda2hs

To run the demo executable, just launch `cabal run demo`.

To test out your library in a REPL, use `cabal repl project`.
