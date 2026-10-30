-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/RunOne/KeySendRound.lean: THEOREMS. **The first written round of a sending's stretch is the round of seeds (SeedRound), from what a frame knows of a stretch: round by round the entry is
the declared round's, and the kind is that of the entry's name.**
  kind_seed        the format's kind of the name "SEND seed" is «seeds»
  seedRound_of     a written round whose entry is a declared round's, that round being the kind K1's first, and whose kind is that of the entry's name: SeedRound
  idx_rounds | msg_rounds | w_rounds   the three joined blocks declare just K1's two rounds
What is not claimed. That a frame's stretch is so: that is the frame's law on its cuts. Nothing on soundness.

-/
import Johnson.RunOne.KeySendGood
import Decl.Declared

set_option autoImplicit false

namespace Johnson.RunOne.KeySendGood

open OnBytes OnBytes.Params VerifiableInference.Desc.Key OnBytes.Maker
open VerifiableInference.Desc (Block)
open VerifiableInference.Desc.K1 (Par seedEntry)

theorem kind_seed : Fmt.kindOf "SEND seed" = some .seeds := by decide

theorem seedRound_of (P : Par) (r : Fmt.DeclaredRound) (d : RDT) (hr : (VerifiableInference.Desc.K1.rounds P)[0]? = some r) (he : d.entry = r.entry)
    (hk : Fmt.kindOf r.entry.name = some d.kind) : SeedRound P d := by
  have e : r = { entry := seedEntry P } := (Option.some.inj hr).symm
  subst e
  refine ⟨he, ?_⟩
  have h2 : Fmt.kindOf "SEND seed" = some d.kind := hk
  rw [kind_seed] at h2
  rw [← Option.some.inj h2]
  decide

variable {β Cl : Type}

theorem idx_rounds (one : OneTime) (N : Pieces) (groups : List (List Nat)) :
    (sendIndexMasks (β := β) (Cl := Cl) one N groups).rounds = VerifiableInference.Desc.K1.rounds (sendingPar one N.idx "the index masks" #[one.indexMasks] groups) :=
  List.append_nil _

theorem msg_rounds (one : OneTime) (N : Pieces) (groups : List (List Nat)) :
    (sendOwnMessage (β := β) (Cl := Cl) one N groups).rounds =
      VerifiableInference.Desc.K1.rounds (sendingPar one N.msg "the lookups' own message and what rides with it" (Wf.messageOf one.ranges) groups) :=
  List.append_nil _

theorem w_rounds {one : OneTime} {N : Pieces} {sent : Nat} {groups : List (List Nat)} {bw : Block (ChainState β) Cl} {msg : Array OracleNotice}
    (hm : linMessageW one.lin = some msg) (hb : sendW one N sent groups = some bw) :
    bw.rounds = VerifiableInference.Desc.K1.rounds (sendingPar one N.w "W and what rides with it" msg groups) := by
  unfold sendW at hb
  rw [hm] at hb
  rw [← Option.some.inj hb]
  rfl

end Johnson.RunOne.KeySendGood

#print axioms Johnson.RunOne.KeySendGood.kind_seed
#print axioms Johnson.RunOne.KeySendGood.seedRound_of
#print axioms Johnson.RunOne.KeySendGood.idx_rounds
#print axioms Johnson.RunOne.KeySendGood.msg_rounds
#print axioms Johnson.RunOne.KeySendGood.w_rounds
