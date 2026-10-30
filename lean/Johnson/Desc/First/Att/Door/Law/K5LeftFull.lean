-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Att/Door/Law/K5LeftFull.lean: kind K5: **WHAT IS LEFT OF THE TIE AT THE KIND's PLACE, WITH NO TEST ON A LIST AMONG IT**: K5LeftAt (Door/Law/K5LeftAt.lean) less its nine fields [L] and K5Owes' four on the
table's lists: these thirteen are decided by Lean's kernel at the full written lists (Door/Law/K5ListsFull.lean; K5TableFull.lean), where the base's list of extra public tests is empty and the filling's is the closed one of the filling (the name moreOver9):
two equations, which come in as fields.
THE THIRTEEN DECISIONS AND THE NAME moreOver9 READ THE Johnson/Desc/First/Close/Law/FillRowFirst.lean OF THE BUILD IN WHICH THEY ARE COMPILED: THEY ARE DECIDED ANEW IN EACH
BUILD; a pass over one text of that file says nothing of another.

Compiled with the whole library.
(Where this and lean/THEOREM.md differ, the page holds.)



Main names:
  K5LeftFull … q Wv g ℓ: 20 fields: [E] 7 (K5LeftAt's five; moreBase; moreIs) · [Q] 5 · [N] 6 · [B] 1 · [W] 1: K5Rest (its 41 fields bear their own tags: Door/Law/K5AtMgPaid.lean).
  K5LeftFull.toAt: g < 12 → K5LeftFull → K5LeftAt. k5_tiedAtR_leftFull: the tie from it and K5Along's seven.
IS IT EMPTY HERE? AN IMPLICATION OVER LETTERS. NO MEMBER OF K5LeftFull IS SHOWN AT ANY LETTERS.
Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Att.Door.Law.K5LeftAt
import Johnson.Desc.First.Att.Door.Law.K5TableFull

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace H2K5.Door
open Cb Cb.Fo Cb.LdLkp OnBytes OnBytes.Model OnBytes.Model.Road OnBytes.Maker OnBytes.Flat Johnson.Pack Run
open VerifiableInference.Desc VerifiableInference.Desc.First VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First.Look (Sent JAtt lookAt sigListCalls)
open VerifiableInference.Desc.K13.Law (DataK13)
open VerifiableInference.Desc.First.Att.P
open VerifiableInference.Desc.K12.Door (Laid)
open OnBytes.Road.L5 (Zs)

section
variable {Pp Xi Cells Tok : Type} {nR : ℕ} {Fr : Frame}
  (Mg Mg0 : Meaning Pp (Wit Cells Tok MsgT)) (D : PubData) (Dn : Sent) (G0 : FileDescription Xi) (arr : ℕ → ℕ → ℕ)
  (smp : Pp × S → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf Dn.codes s.l).om i).Smp) (ms : List Mem)
  (decT : (ℕ → Option (ℕ × List UInt64)) → Pp × S → Option Cells) (Ld : Laid) (Ms : List OracleShape)
  (q : Piece (ckP .two) Fr (Pp × S) Claim (Wit Cells Tok MsgT)) (Wv : Verify.Public) (g : ℕ)
  (ℓ : K5Pick Pp Cells Tok nR Fr Dn)

/-- **WHAT IS LEFT OF THE TIE AT THE KIND's PLACE OF GROUP g, THE TESTS ON THE LISTS PAID.** -/
structure K5LeftFull : Prop where
  /-- [E] fifteen equations on the wider filling. -/
  mgIs : MgIs (mgPlus Mg Mg0.more D Ld Ms Mg0.pub Dn.codes) Mg0 D Dn.codes G0 arr smp ms decT ℓ.in0 ℓ.c5 Ld Ms ℓ.D13
  /-- [E] four equations on the wider filling: what it says of the claims on linear forms, of a lookup's worth and of a constraint. -/
  mgGains : MgGains (mgPlus Mg Mg0.more D Ld Ms Mg0.pub Dn.codes) Dn.codes arr ms D.Rd D.runs (Stated.of (uBySort ℓ.uL (uArm Wv) ℓ.uH)) D.N ℓ.wt
    (2 * g + 1) ℓ.x ℓ.a.S ℓ.a.seam.tl Dn ℓ.rad ℓ.seat arr
  /-- [E] five ties of the composed data's letters to the kind's. -/
  dataIs : DataIs D Wv LFullK (2 * g + 1)
  /-- [E] three ties of the composed data to what the plan sends. -/
  dataSent : DataSent D Dn.codes Dn
  /-- [E] the narrower filling's public tests are the function with code, over the base's. -/
  pubIs : Mg.pub = pubAll D Mg0.pub
  /-- [Q] the piece looks back at nothing. -/
  back : q.back = []
  /-- [Q] the piece's error is the capped union bound over its rounds. -/
  err : q.err = Iop.Err.cap 128 (uLT (ckP .two) q.ds)
  /-- [Q] the piece's rounds are the plan's. -/
  rounds : List.Forall₂ RoundAsG q.ds (rounds (parO Wv (2 * g + 1) ℓ.a ℓ.before))
  /-- [Q] the seated sub-protocol is the kind's, dressed. -/
  seatOf : SeatOf ℓ.blk ℓ.B
  /-- [Q] the piece's verifier is that sub-protocol's, lifted over the public part. -/
  runs : q.b = (below ℓ.B).lift Prod.snd fun t s => (t.1, s)
  /-- [N] the public parameters are a plan's. -/
  planIs : PlanIs Wv
  /-- [N] profile 4. -/
  p4 : Wv.p4 = true
  /-- [N] the group's attention plan. -/
  planAt : Wv.A[g]? = some ℓ.a
  /-- [N] the place of the segment's lookup argument. -/
  lookC : lookAt Wv (2 * g + 1) false = some ℓ.x
  /-- [N] the place of its digits' lookup argument. -/
  lookD : lookAt Wv (2 * g + 1) true = some ℓ.xd
  /-- [N] seven facts on the plan of the segment's own rounds. -/
  plan : K5Plan (parO Wv (2 * g + 1) ℓ.a ℓ.before).own (2 * g + 1) (Look.P.ofPlace (Params.settingOf Wv.P.frame) false ℓ.x)
    (Look.P.ofPlace (Params.settingOf Wv.P.frame) true ℓ.xd) ℓ.hS (Forest.elems ℓ.a.fs) ℓ.kr ℓ.a.ns
  /-- [B] the kind's sub-protocol sends no oracle message: two equations on the table's numbers. -/
  book : K5Book D.N ⟨1, some (2 * g + 1), 3, .K5⟩ ⟨1, some (2 * g + 1), 4, .K1⟩
  /-- [E] the base's list of extra public tests is empty. -/
  moreBase : Mg0.more = {}
  /-- [E] the filling's list of extra public tests is the closed one (moreOver9). -/
  moreIs : Mg.more = (moreOver9 {}).strike leavesName
  /-- [W] K5Rest: 41 fields, each with its own tag (Door/Law/K5AtMgPaid.lean). -/
  rest : K5Rest (Fr := Fr) (mgPlus Mg Mg0.more D Ld Ms Mg0.pub Dn.codes) Mg0 D Dn arr smp ms decT ℓ.in0 Ld Ms ℓ.D13 q.base Wv g ℓ.before ℓ.a ℓ.x LFullK
    ⟨1, some (2 * g + 1), 3, .K5⟩ ℓ.rad ((openSets LFullK PFullK (start LFullK))[14 * (2 * g + 1) + 4]?.getD [])
    ((pubSets (morePlus Mg0.more) LFullK PFullK)[14 * (2 * g + 1) + 4]?.getD [])
    ℓ.seat ℓ.smpR ℓ.lk ℓ.Lk ℓ.same ℓ.blk ℓ.claimC ℓ.nm ℓ.Hd ℓ.bsW ℓ.dP ℓ.body ℓ.Zof

variable {Mg Mg0 D Dn G0 arr smp ms decT Ld Ms q Wv g ℓ}

/-- **The thirteen tests on the lists are paid at the full written lists.** -/
theorem K5LeftFull.toAt (H : K5LeftFull Mg Mg0 D Dn G0 arr smp ms decT Ld Ms q Wv g ℓ) (hg : g < 12) :
    K5LeftAt Mg Mg0 D Dn G0 arr smp ms decT Ld Ms q Wv g ℓ where
  mgIs := H.mgIs
  mgGains := H.mgGains
  dataIs := H.dataIs
  dataSent := H.dataSent
  pubIs := H.pubIs
  back := H.back
  err := H.err
  rounds := H.rounds
  seatOf := H.seatOf
  runs := H.runs
  planIs := H.planIs
  p4 := H.p4
  planAt := H.planAt
  lookC := H.lookC
  lookD := H.lookD
  plan := H.plan
  book := H.book
  place := ⟨rfl, rfl, sub_full hg, rfl, rfl⟩
  next := next_full hg
  asks := by rw [H.moreBase]; exact asks_full hg
  readsOpen := readsOpen_full
  rowsApart := rowsApart_full
  riders := riders_full hg
  doors := by rw [H.moreIs, H.moreBase]; exact doors_full hg
  doors' := by rw [H.moreIs, H.moreBase]; exact doors_full' hg
  openBehind := by rw [H.moreIs, H.moreBase]; exact hopen_full' hg
  owes := ⟨by rw [H.moreBase]; exact k5Table_full hg, H.rest⟩

/-- **The tie at the kind's place of group g, from what is left beside the lists and K5Along's seven.** -/
theorem k5_tiedAtR_leftFull [Nonempty Pp] (H : K5LeftFull Mg Mg0 D Dn G0 arr smp ms decT Ld Ms q Wv g ℓ) (hg : g < 12)
    (Rch : ℕ → (Pp × S) × Fr.E.Str → Prop) (A : K5Along Rch Ld Ms Dn)
    (Ee : (Pp × S) × Fr.E.Str → (Pp × S) × Fr.E.Str → Wit Cells Tok MsgT → Wit Cells Tok MsgT) (hEe : ∀ u v w, Ee u v w = w)
    (hs : HandsOn Rch (14 * (2 * g + 1) + 4) q) :
    TiedAtR D.N Mg LFullK PFullK (fun u => u) Rch (14 * (2 * g + 1) + 4) (q.withMap Ee) :=
  k5_tiedAtR_left (H.toAt hg) hg Rch A Ee hEe hs

end

end H2K5.Door

#print axioms H2K5.Door.K5LeftFull.toAt
#print axioms H2K5.Door.k5_tiedAtR_leftFull
