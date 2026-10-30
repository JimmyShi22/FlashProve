-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/Tw/K2C/SmpLikeNew.lean: code switching (the kind K2): behind a switch, the named
reader of OOD samples gives, at each new member, the sample that the switch's law reads, up to the
OOD seed's values. Theorems with their proofs. No block imports this file.

Why. The ties t2 and t3 of the switch's law take as a premise `K2.SmpLike` (StringsNew.lean) at the
table's reader of OOD samples and at `newSmp` (Johnson/Top/H0/K2Caller/BehindPaid.lean). At the
closed constant that reader is `smpNamed cs seats` (Johnson/Desc/Sound/SmpNamed.lean). Both readers
take the first stored sample row of a message as a linear form, pick BY CHOICE an OOD seed with that
sample map, and take the stored target for the OOD answers. So they agree up to the seed's values,
if they read the same message.

Main names. seats: the planned list of seats, in the order of sending. seatN i: the seat of the new
member i. n0: the number of the messages in front of the switch. s': the verifier's state behind.
  `smpLike_new`: `K2.SmpLike r.cs (smpNamed r.cs seats) (z, s') ⟨r.l, seatN⟩ (newSmp n0 s')`, from:
    hq: each seatN i is in seats · hnum: its place there is n0 + i · hf: the first stored sample row
    of message n0 + i, as a form, is the sample map of some OOD seed.
  `smpLike_of_list`: the same with hq and hnum from two facts on the plain list (`nums_of_list`,
    SmpForms.lean): seats has no repeats, and holds seatN i at place n0 + i. `smpLike_of_test`: from
    the test with code `K2.newSeatsB`.
  `forms_at_yes`: hf at an accepting step of the switch (`K2.AtYes`), by `seedIs_sig`
    (Johnson/Top/H0/K2Hands/SeedJoint.lean).
  `smpLike_at_yes`: the three together.

Limits. `smpNamed` takes a message's number from the planned list, not from the state's book of
trees: so hnum is a fact on that list and on n0. It is shown here at no list. Both OOD seeds are by
choice: nothing says that either is the seed that was drawn; their sample maps are one. Nothing on
the kept members. Where r.l is empty the statement says nothing. Nothing on soundness.

-/
import Johnson.Top.H0.Tw.K2C.SmpForms
import Johnson.Top.H0.Tw.K2C.StringsNew
import Johnson.Top.H0.K2Caller.BehindPaid
import Johnson.Desc.Sound.SmpNamed

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2Caller
open OnBytes OnBytes.Slice OnBytes.Params OnBytes.Plan OnBytes.Flat OnBytes.Maker Iop Cb
open Johnson.Pack Johnson.Top.H OnBytes.Tie.Pv.Switch
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First.K2Hands
open _root_.Tw.K2 (switchNotices)

variable {P : Type} {r : SwRow}

/-- **At the new members the named reader gives the law's sample, up to the seed's values.** -/
theorem smpLike_new (seats : List (ℕ × ℕ)) (seatN : Fin r.l.length → ℕ × ℕ) (n0 : ℕ) (z : P)
    (s' : Rec) (hq : ∀ i, seatN i ∈ seats)
    (hnum : ∀ i : Fin r.l.length, seats.idxOf (seatN i) = n0 + i.val)
    (hf : ∀ i : Fin r.l.length, ∃ ρ : ((sigOf r.cs r.l).om i).Z.D,
      (K2.formsAt r.cs (r.l.get i).1 s'.st (n0 + i.val) :
        Option (((sigOf r.cs r.l).om i).Z.S → ((sigOf r.cs r.l).om i).C.J → GE)) =
        some (((sigOf r.cs r.l).om i).Z.mat ρ)) :
    K2.SmpLike r.cs (smpNamed r.cs seats) (z, s') ⟨r.l, seatN⟩ (fun o => newSmp n0 s' o) := by
  intro i
  obtain ⟨ρ, hρ⟩ := hf i
  obtain ⟨zz, hz, hv, ha⟩ := K2.smpAt_like r.cs (r.l.get i).1 (r.l.get i).2 s'.st (n0 + i.val) ρ
    ((K2.forms_two_texts r.cs (r.l.get i).1 s'.st (n0 + i.val)).trans hρ)
  refine ⟨zz, ?_, ?_, ?_⟩
  · rw [smpNamed_at r.cs seats (z, s') ⟨r.l, seatN⟩ i (hq i)]
    show K1.smpAt r.cs (r.l.get i).1 (r.l.get i).2 s'.st (seats.idxOf (seatN i)) = some zz
    rw [hnum i]
    exact hz
  · exact hv.trans (val_congr _ _ _ (newSmp_mat n0 s' i ρ hρ)).symm
  · show zz.2 = (K2.ansAt s'.st (n0 + i.val)).getD fun _ => 0
    rw [← K2.ans_two_texts, ha]
    rfl

/-- The same, from two facts on the plain list. -/
theorem smpLike_of_list (seats : List (ℕ × ℕ)) (seatN : Fin r.l.length → ℕ × ℕ) (n0 : ℕ) (z : P)
    (s' : Rec) (hnd : seats.Nodup)
    (hs : ∀ i : Fin r.l.length, seats[n0 + i.val]? = some (seatN i))
    (hf : ∀ i : Fin r.l.length, ∃ ρ : ((sigOf r.cs r.l).om i).Z.D,
      (K2.formsAt r.cs (r.l.get i).1 s'.st (n0 + i.val) :
        Option (((sigOf r.cs r.l).om i).Z.S → ((sigOf r.cs r.l).om i).C.J → GE)) =
        some (((sigOf r.cs r.l).om i).Z.mat ρ)) :
    K2.SmpLike r.cs (smpNamed r.cs seats) (z, s') ⟨r.l, seatN⟩ (fun o => newSmp n0 s' o) :=
  smpLike_new seats seatN n0 z s' (K2.nums_of_list seats seatN n0 hnd hs).1
    (K2.nums_of_list seats seatN n0 hnd hs).2 hf

/-- The same, from the test with code on the plain list. -/
theorem smpLike_of_test (seats : List (ℕ × ℕ)) (seatN : Fin r.l.length → ℕ × ℕ) (n0 : ℕ) (z : P)
    (s' : Rec) (ht : K2.newSeatsB seats seatN n0 = true)
    (hf : ∀ i : Fin r.l.length, ∃ ρ : ((sigOf r.cs r.l).om i).Z.D,
      (K2.formsAt r.cs (r.l.get i).1 s'.st (n0 + i.val) :
        Option (((sigOf r.cs r.l).om i).Z.S → ((sigOf r.cs r.l).om i).C.J → GE)) =
        some (((sigOf r.cs r.l).om i).Z.mat ρ)) :
    K2.SmpLike r.cs (smpNamed r.cs seats) (z, s') ⟨r.l, seatN⟩ (fun o => newSmp n0 s' o) :=
  smpLike_of_list seats seatN n0 z s' (K2.newSeats_of_test seats seatN n0 ht).1
    (K2.newSeats_of_test seats seatN n0 ht).2 hf

/-- **At an accepting step of the switch the stored forms are sample maps.** -/
theorem forms_at_yes {p : K2.P2} {s s' : Rec} {r₁ r₂ : Fmt.RoundView}
    {gs : List (List (ℕ × List UInt64))} {x : _root_.Tw.K2.Front} {y : _root_.Tw.K2.Sent}
    {S3 : Statement} {Y : Array E} {rows : List OnBytes.Row} {G : Group} {c : Code}
    (A : K2.AtYes p s s' r₁ r₂ gs x y S3 Y rows G c) (n0 : ℕ) (hc : x.st.codes = r.cs)
    (hn : x.st.oracles.size = n0) (hT : Tied r.l (switchNotices x.T x.others))
    (sd : (seedsOf r.cs r.l).D) (J : JointIs r.cs r.l r₁ sd) :
    ∀ i : Fin r.l.length, ∃ ρ : ((sigOf r.cs r.l).om i).Z.D,
      (K2.formsAt r.cs (r.l.get i).1 s'.st (n0 + i.val) :
        Option (((sigOf r.cs r.l).om i).Z.S → ((sigOf r.cs r.l).om i).C.J → GE)) =
        some (((sigOf r.cs r.l).om i).Z.mat ρ) := by
  subst hn
  have key : ∀ (cs : Codes), x.st.codes = cs → ∀ (sd : (seedsOf cs r.l).D),
      JointIs cs r.l r₁ sd → ∀ i : Fin r.l.length, ∃ ρ : ((sigOf cs r.l).om i).Z.D,
      (K2.formsAt cs (r.l.get i).1 s'.st (x.st.oracles.size + i.val) :
        Option (((sigOf cs r.l).om i).Z.S → ((sigOf cs r.l).om i).C.J → GE)) =
        some (((sigOf cs r.l).om i).Z.mat ρ) := by
    rintro _ rfl sd J i
    exact ⟨_, seedIs_sig A r.l hT sd J i⟩
  exact key r.cs hc sd J

/-- **The three together**: at an accepting step of the switch. -/
theorem smpLike_at_yes {p : K2.P2} {s s' : Rec} {r₁ r₂ : Fmt.RoundView}
    {gs : List (List (ℕ × List UInt64))} {x : _root_.Tw.K2.Front} {y : _root_.Tw.K2.Sent}
    {S3 : Statement} {Y : Array E} {rows : List OnBytes.Row} {G : Group} {c : Code}
    (A : K2.AtYes p s s' r₁ r₂ gs x y S3 Y rows G c) (n0 : ℕ) (hc : x.st.codes = r.cs)
    (hn : x.st.oracles.size = n0) (hT : Tied r.l (switchNotices x.T x.others))
    (sd : (seedsOf r.cs r.l).D) (J : JointIs r.cs r.l r₁ sd) (seats : List (ℕ × ℕ))
    (seatN : Fin r.l.length → ℕ × ℕ) (z : P) (ht : K2.newSeatsB seats seatN n0 = true) :
    K2.SmpLike r.cs (smpNamed r.cs seats) (z, s') ⟨r.l, seatN⟩ (fun o => newSmp n0 s' o) :=
  smpLike_of_test seats seatN n0 z s' ht (forms_at_yes A n0 hc hn hT sd J)

end VerifiableInference.Desc.First.K2Caller

#print axioms VerifiableInference.Desc.First.K2Caller.smpLike_new
#print axioms VerifiableInference.Desc.First.K2Caller.smpLike_of_list
#print axioms VerifiableInference.Desc.First.K2Caller.smpLike_of_test
#print axioms VerifiableInference.Desc.First.K2Caller.forms_at_yes
#print axioms VerifiableInference.Desc.First.K2Caller.smpLike_at_yes
