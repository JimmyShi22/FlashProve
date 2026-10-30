-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Flat/Silent.lean: provers that send each round's fixed message, as values of the honest
provers that the object with records holds (`Files.Provers`, OnBytes/Flat/Object.lean).

Definitions. The library's object `HolographicProtocol` holds honest provers of its three protocols as data. No
statement on soundness asks anything of them (OnBytes/Flat/Object.lean). So that a description can
be written out whole, here are values: in every round the fixed message of the round's format
(`Round.dOrc`, `Round.dPlain`) is sent; the field `ext` alone is no placeholder: it is the
configuration's encoder at the message that holds the index. THEY ARE NOT THE PROVER PROGRAM:
nothing on completeness or on hiding can be said with them.

"Silent" here means: a prover that does send in every round, namely the round's fixed message. It is
neither the "silent rounds" of a file (the front round, the joining round and the seam:
OnBytes/Maker/SilentParts.lean; `silK`, `silP`, OnBytes/Flat/FilesAt.lean) nor the library's
`SStrat.silent` (Blocks/Batch/KitHon.lean).

Limits: in the statements the provers are a letter P. `F.fixedMessageProvers` SENDS FIXED MESSAGES: IT IS NOT THE
PROVER PROGRAM. The online and offline honest provers fall back on it where a function that makes
them refuses (`onlineProver`, `offlineProver`, E2E/TheHonestProver.lean). At it the sets of withheld
verifier messages are empty, so completeness (`CompleteR`, Hiop/RecInterface.lean) would say that
the verifier accepts the transcript of fixed messages at every valid input and all randomness:
`CompleteR`, and with it `PropsH` and `PropsR`, which hold it, are not to be asked at
`F.withProvers F.fixedMessageProvers`: a theorem that asked them there would be likely to speak of nothing.

Main names: `silent s b`, `silent0 s A`, `silentJ s A` (strategies); `F.fixedMessageProvers : F.Provers`.
Terms: lean/GLOSSARY.md.

-/
import OnBytes.Flat.Object

set_option autoImplicit false

namespace OnBytes.Flat
open Iop Hiop

/-- In every round the fixed message; at the end b. -/
def silent {β : Type} : (s : Shape) → β → Strat s β
  | [], b => b
  | r :: s, b => ((r.dOrc, r.dPlain), fun _ => silent s b)

/-- The shared part of the fixed messages. -/
def silent0 : (s : Shape) → (A : RoundSplits s) → SStrat s A
  | [], _ => ()
  | r :: s, (a, A) => ((a.split (r.dOrc, r.dPlain)).1, fun _ => silent0 s A)

/-- A slot's part of the fixed messages. -/
def silentJ : (s : Shape) → (A : RoundSplits s) → LStrat s A
  | [], _ => ()
  | r :: s, (a, A) => ((a.split (r.dOrc, r.dPlain)).2, fun _ => silentJ s A)

namespace Files
variable {C : ConfigurationWithOutOfDomainSample} (F : Files C)

/-- Provers that send the fixed messages. -/
def fixedMessageProvers : F.Provers where
  hT :=
    { Coin := Unit
      ext := fun w => C.enc (C.hold w.1 w.2.1.1) w.2.1.2
      strat := fun _ _ _ => OnBytes.Flat.silent _ ()
      Bad := ∅
      Hid := fun _ _ => ∅ }
  hL :=
    { Coin := Unit
      ext := fun w =>
        (C.enc (C.hold w.1 w.2.1.1.1) w.2.1.1.2, C.enc (C.hold w.1 w.2.2.1.1) w.2.2.1.2)
      strat := fun _ _ _ => OnBytes.Flat.silent _ ()
      Bad := ∅
      Hid := fun _ _ => ∅ }
  hB :=
    { Coin0 := Unit
      Coin := Unit
      ext := fun w => C.enc (C.hold w.1 w.2.1.1) w.2.1.2
      strat0 := fun _ _ => silent0 _ _
      strat := fun _ _ _ _ => silentJ _ _
      Bad := ∅
      Hid := fun _ _ => ∅
      stop0 := fun _ => false }

end Files
end OnBytes.Flat
