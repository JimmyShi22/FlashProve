-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/ChecksWithHashAsArgument/M/Params/Configure.lean: CUT OUT BY A PROGRAM FROM A TEXT WRITTEN BY HAND: the
program chooses the declarations that differ from the port's and turns names; it does not make the
turn over m. The definitions of OnBytes/Params/Configure.lean that hash, or hand a hash on, written
once more over a monad m in which the hash is asked. The port's own file is untouched. What does not
hash is the port's own. The text written by hand is this project's authors' own rewriting of the
port's file.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.Params.Configure

namespace OnBytes.TwoPort.M.Params

open OnBytes.Params

/-- The digest of the public files, the parameter file first. -/
def configurationDigest {m : Type → Type} [Monad m]
    (hh : Nat → Nat → Nat → ByteArray → ByteArray → m ByteArray) (files : List ByteArray) :
    m ByteArray :=
  Fmt.configDigestW hh files

end OnBytes.TwoPort.M.Params
