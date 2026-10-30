-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/ChecksWithHashAsArgument/M/Model/VerifyChains.lean: CUT OUT BY A PROGRAM FROM A TEXT WRITTEN BY HAND: the
program chooses the declarations that differ from the port's and turns names; it does not make the
turn over m. The definitions of OnBytes/Model/VerifyChains.lean that hash, or hand a hash on,
written once more over a monad m in which the hash is asked. The port's own file is untouched. What
does not hash is the port's own. The text written by hand is this project's authors' own rewriting
of the port's file. THE TWINS OF MODEL/ (Verify.lean, VerifyChains.lean, VerifyStages.lean: sixteen
definitions). ONE TIE TO THE PORT: at the identity monad, `formatHashFastForm` and, for the request file's
digest, `fun b => secondHashFunctionTree b`, each of the sixteen has the value of the port's of the same name at
all arguments (`namedT`: of `named`; `partCall`: with the stage's run a letter on each side, the two
related): the theorems whose names end in `_port`, and `relX_namedT`, of
OnBytes/ChecksWithHashAsArgument/M/AtPort/Spine.lean. For the twins at another hash see
OnBytes/ChecksWithHashAsArgument/M/AtPort/SpineAt.lean [not in this library], SpinePass.lean [not in this library]
and Calls.lean, whose heads name their premises; over another monad, or with another function for
the request file's digest, see the statements of OnBytes/ChecksWithHashAsArgument/M/Model/SpineHom.lean and
SpineKeeps.lean. The list is not whole, and nothing of it is summed up here. That the text is the
port's with a letter for the hash is held by eye. That `hh` reaches every call of the format's hash
is no theorem. The second hash function's other calls are fixed in the text: no argument stands for
them.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.Model.VerifyChains
import OnBytes.ChecksWithHashAsArgument.M.Chain.EngineM
import OnBytes.ChecksWithHashAsArgument.M.Chain.Reader
import OnBytes.ChecksWithHashAsArgument.M.Chain.Session
import OnBytes.ChecksWithHashAsArgument.M.Chain.Why
import OnBytes.ChecksWithHashAsArgument.M.Entry.Table
import OnBytes.ChecksWithHashAsArgument.M.Params.Configure
import OnBytes.ChecksWithHashAsArgument.M.Proof.File
import OnBytes.ChecksWithHashAsArgument.M.Proof.Place
import OnBytes.ChecksWithHashAsArgument.M.Proof.Reading
import OnBytes.ChecksWithHashAsArgument.M.Proof.Tail

namespace OnBytes.TwoPort.M.Model.Verify

open OnBytes.Model OnBytes.Model.Verify

open OnBytes.Model.Stages

/-- The digest of the three configuration files that every chain binds. The files come in the order
parameter file, layout file, scale file. -/
def configuration {m : Type → Type} [Monad m] (hh : HashM m) (pol layout KL : ByteArray) :
    m ByteArray :=
  Params.configurationDigest hh [pol, layout, KL]

end OnBytes.TwoPort.M.Model.Verify
