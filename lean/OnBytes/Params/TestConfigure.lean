-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Params/TestConfigure.lean: the whole road from the public files' numbers to the parameter
bytes of the seven chains, at the small example.

The lines are those of prover/examples/target_small_f2_roomy/policy.txt. The model's shapes are filled in by hand (OnBytes/Params/TestDerive.lean,
OnBytes/Plan/TestKeyOneTime.lean). The layout is left empty, since it is long; it enters the first
chain's bytes as an item and nothing else. So six chains are held by the digests of their parameter
bytes, and the first chain by its plan. One range check is made up. The digests that are expected
were taken from a run on that example of a copy of the C++ verifier (not in this repository) that
writes out what it hashes. Each test is checked when the file compiles. The file is no part of the
program.
-/
import OnBytes.Params.Configure
import OnBytes.Params.TestDerive
import OnBytes.Plan.TestKeyOneTime

namespace OnBytes.Params.TestConfigure

/-- The small example's shapes. -/
def shapes : Option Shapes :=
  Plan.TestKeyOneTime.shape.map fun r =>
    { sub := TestDerive.subWithRounds, layout := ⟨List.replicate 5 []⟩,
      identifiers := [1, 4, 2, 5, 3], ranges := r,
      rangeChecks := [⟨64, 512, 128, 129, 2 ^ 22, (11, 12)⟩] }

/-- What `configure` makes of the small example when so many bits are asked of every round. -/
def made (change : Shapes → Shapes := id) (bits : Nat := 128) : Option (Except String Configured) :=
  TestFile.smallLines.bind fun l => shapes.map fun x =>
    configure l (change x) TestFile.smallCfg bits

/-- The digest of parameter bytes, in hexadecimal digits. -/
def digest (b : ByteArray) : String := Fmt.hex (Fmt.paramsDigestW (m := Id) formatHashFastForm b)

/-- The name of a refusal; the empty string if there is none. -/
def refusal (x : Option (Except String Configured)) : String :=
  match x with
  | some (.error e) => e
  | _ => ""

#guard (made.bind (·.toOption)).any fun c =>
  digest c.keyOneTime == "859ef8873838b71646933101a10588f544016f7cfbfad3a784524407e01abc19" &&
  digest c.keyShared == "1f65b490e5071b268d94a37af4bb23bb21227032982a0be756f8097d5e53817a" &&
  digest c.keySecond == "50b081d0b33589b3964f4a8d0d7227676d4495c676200a3a3d9da67f7d5fe474" &&
  digest c.entryLink == "024a450069cd46ebdeb048d9ec5c3860e8eb16cb4be3a42c0d72f3c33e7ce6d7" &&
  digest c.shared == "6e18903daad8dccc4414257bd8b7d66423a3a4bc8849915d46866b7c19860f6e" &&
  digest c.second == "80c1a7c7d0f4c3304ef58d9d791c128152c28f423474873a3e787be0f6025cea" &&
  needsWork c.proof && needsWork c.key && needsWork [c.entry]
-- more bits are asked than the parameter file's target has
#guard refusal (made id 129) == "security-bits"
-- no range check; an identifier too few
#guard refusal (made fun x => { x with rangeChecks := [] }) == notAdmitted
#guard refusal (made fun x => { x with identifiers := [1, 4, 2, 5] }) == notAdmitted
-- a range check that an honest prover fails too often
#guard refusal (made fun x => { x with rangeChecks := [⟨64, 512, 128, 129, 2 ^ 13, (7, 7)⟩] }) ==
  notAdmitted

end OnBytes.Params.TestConfigure
