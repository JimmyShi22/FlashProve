-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Att/Door/Law/K5LeftAt.lean: kind K5: **TWO OF THE THREE PIECES OF THE ROAD TO THE KIND's LAW, CALLED TOGETHER, OVER LETTERS**: the tie at one place from K5Owes and its fellows (k5_tiedAtR_owes,
Door/Law/K5TiedOwes.lean) and what the bridge spends of "reached" from K5Along's seven (K5Along.facts5, Door/Law/K5Along.lean; hbare_of_reached | hleft_of_reached, Door/Law/K5ReachedPlus.lean), AT THE FULL WRITTEN LISTS
(LFullK | PFullK, Door/Law/K05KindR.lean) and the kind's twelve numbers 14 (2 g + 1) + 4.

Main names:
  K5Pick: THE LETTERS THAT THE PAYER PICKS: every letter of k5_tiedAtR_owes that stands neither in its conclusion nor among the composed filling's own parameters, AND THAT SOME PREMISE READS. One structure of data.
    (Seven letters that no premise reads have left it: Cl · claim · Ex · Wp · α · plJ · yOf: k5_tiedAtR_left lays each at a plain member of its type.)
  K5LeftAt … q Wv g ℓ: EVERY PREMISE OF k5_tiedAtR_owes THAT IS NOT PAID HERE, a field each, tagged by kind:
    [E] an equation on the filling or the data · [Q] on the description's piece q · [N] on the plan · [B] on the table's numbers · [L] a test on the written lists alone · [W] K5Owes (its 45 fields bear their own tags).
  k5_tiedAtR_left: K5LeftAt → K5Along → g < 12 → an extractor that lays nothing → HandsOn → TiedAtR at the number.
PAID HERE, of k5_tiedAtR_owes' premises: hk (k5_at_full) · F (K5Along.facts5, its two equations out of DataSent) · hbare · hleft · hlow (it is K5Owes' low0 at K5Owes' sent).
Compiled with the whole library.
(Where this and lean/THEOREM.md differ, the page holds.)


IS IT EMPTY HERE? AN IMPLICATION OVER LETTERS. NO MEMBER OF K5LeftAt IS SHOWN AT ANY LETTERS.
Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Att.Door.Law.K5TiedOwes
import Johnson.Desc.First.Att.Door.Law.K5ReachedPlus
import Johnson.Desc.First.Att.Door.Law.K5Along
import Johnson.Desc.First.Att.Door.Law.K05KindR

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

/-- **The letters that the payer picks.** -/
structure K5Pick (Pp Cells Tok : Type) (nR : ℕ) (Fr : Frame) (Dn : Sent) where
  Ix : Type
  in0 : Pp × S → Bool
  c5 : Pp → Bool
  D13 : DataK13 Pp (Wit Cells Tok MsgT) nR
  before : List (ℕ × ℕ)
  a : Attention.Plan
  x : Look.Place
  xd : Look.Place
  rad : OracleShape → Nat
  uL : ℕ → UFn
  uH : ℕ → UFn
  wt : ℕ → Pp × S → Strs → Wit Cells Tok MsgT → Prop
  seat : Fin (sigListCalls Dn rad x.link).length → ℕ × ℕ
  smpR : Array OnBytes.Oracle × OnBytes.TreeBook → (i : Fin (sigListCalls Dn rad x.link).length) →
    Option ((sigOf Dn.codes (sigListCalls Dn rad x.link)).om i).Smp
  lk : ℕ → Option (Link S Claim)
  Lk : Link S Claim
  same : S → S → Bool
  blk : Block S Claim
  claimC : Aff → Claim
  nm : String
  Hd : Cells → Ix → Prop
  bsW : ℕ → Wit Cells Tok MsgT → Prop
  dP : ℕ → Pp × S → Strs → Wit Cells Tok MsgT → Prop
  body : ℕ → First.Part → Ix → Pp × S → Strs → Wit Cells Tok MsgT → Prop
  Zof : Wit Cells Tok MsgT → Zs
  hS : Forest.Shape
  kr : ℕ
  B : Block S Claim

section
variable {Pp Xi Cells Tok : Type} {nR : ℕ} {Fr : Frame}
  (Mg Mg0 : Meaning Pp (Wit Cells Tok MsgT)) (D : PubData) (Dn : Sent) (G0 : FileDescription Xi) (arr : ℕ → ℕ → ℕ)
  (smp : Pp × S → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf Dn.codes s.l).om i).Smp) (ms : List Mem)
  (decT : (ℕ → Option (ℕ × List UInt64)) → Pp × S → Option Cells) (Ld : Laid) (Ms : List OracleShape)
  (q : Piece (ckP .two) Fr (Pp × S) Claim (Wit Cells Tok MsgT)) (Wv : Verify.Public) (g : ℕ)
  (ℓ : K5Pick Pp Cells Tok nR Fr Dn)

/-- **WHAT IS LEFT OF THE TIE AT THE KIND's PLACE OF GROUP g, AT THE FULL WRITTEN LISTS.** A field a premise of k5_tiedAtR_owes. -/
structure K5LeftAt : Prop where
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
  /-- [L] the place and the one behind it, in the written list of segments. -/
  place : K5Place LFullK (2 * g + 1) ⟨1, some (2 * g + 1), 3, .K5⟩ ⟨1, some (2 * g + 1), 4, .K1⟩
  /-- [L] the place behind. -/
  next : PFullK[14 * (2 * g + 1) + 4 + 1]? = some ⟨1, some (2 * g + 1), 4, .K1⟩
  /-- [L] what the row asks is open in front. -/
  asks : ∀ t ∈ (pubRowOf LFullK ⟨1, some (2 * g + 1), 3, .K5⟩).asks, t ∈ ((pubSets (morePlus Mg0.more) LFullK PFullK)[14 * (2 * g + 1) + 4]?.getD [])
  /-- [L] every row reads what is open. -/
  readsOpen : readsOpen LFullK PFullK (start LFullK) = true
  /-- [L] the rows are apart. -/
  rowsApart : rowsApart LFullK PFullK = true
  /-- [L] the riders' test at the border. -/
  riders : ridersB LFullK PFullK (14 * (2 * g + 1) + 4) (2 * g + 1) = true
  /-- [L] the two lists of extra public tests fit at the border in front. -/
  doors : doorsFitB Mg.more (morePlus Mg0.more) isWideQ LFullK PFullK (14 * (2 * g + 1) + 4) = true
  /-- [L] and at the border behind. -/
  doors' : doorsFitB Mg.more (morePlus Mg0.more) isWideQ LFullK PFullK (14 * (2 * g + 1) + 4 + 1) = true
  /-- [L] what is open behind at the wider list is open at the narrower one, or is one of three names. -/
  openBehind : ∀ t ∈ (pubSets (morePlus Mg0.more) LFullK PFullK)[14 * (2 * g + 1) + 4 + 1]?.getD [],
    t ∈ (pubSets Mg.more LFullK PFullK)[14 * (2 * g + 1) + 4 + 1]?.getD [] ∨ isThreeQ t = true
  /-- [W] K5Owes: 45 fields, each with its own tag (Door/Law/K5AtMgPaid.lean). -/
  owes : K5Owes (Fr := Fr) (mgPlus Mg Mg0.more D Ld Ms Mg0.pub Dn.codes) Mg0 D Dn arr smp ms decT ℓ.in0 Ld Ms ℓ.D13 q.base Wv g ℓ.before ℓ.a ℓ.x LFullK
    ⟨1, some (2 * g + 1), 3, .K5⟩ ℓ.rad ((openSets LFullK PFullK (start LFullK))[14 * (2 * g + 1) + 4]?.getD [])
    ((pubSets (morePlus Mg0.more) LFullK PFullK)[14 * (2 * g + 1) + 4]?.getD [])
    ℓ.seat ℓ.smpR ℓ.lk ℓ.Lk ℓ.same ℓ.blk ℓ.claimC ℓ.nm ℓ.Hd ℓ.bsW ℓ.dP ℓ.body ℓ.Zof

variable {Mg Mg0 D Dn G0 arr smp ms decT Ld Ms q Wv g ℓ}

/-- **The tie at the kind's place of group g, from what is left and K5Along's seven.** -/
theorem k5_tiedAtR_left [Nonempty Pp] (H : K5LeftAt Mg Mg0 D Dn G0 arr smp ms decT Ld Ms q Wv g ℓ) (hg : g < 12)
    (Rch : ℕ → (Pp × S) × Fr.E.Str → Prop) (A : K5Along Rch Ld Ms Dn)
    (Ee : (Pp × S) × Fr.E.Str → (Pp × S) × Fr.E.Str → Wit Cells Tok MsgT → Wit Cells Tok MsgT) (hEe : ∀ u v w, Ee u v w = w)
    (hs : HandsOn Rch (14 * (2 * g + 1) + 4) q) :
    TiedAtR D.N Mg LFullK PFullK (fun u => u) Rch (14 * (2 * g + 1) + 4) (q.withMap Ee) :=
  k5_tiedAtR_owes Mg Mg0 D Dn G0 arr smp ms decT ℓ.in0 ℓ.c5 Ld Ms ℓ.D13 H.mgIs q H.back H.err (fun _ => ()) Wv g ℓ.before ℓ.a ℓ.x ℓ.xd LFullK H.dataIs
    H.dataSent H.planIs H.p4 H.planAt H.lookC H.lookD _ _ H.place ℓ.rad ⟨Unit, Unit, Unit, fun _ _ => ()⟩ Unit (fun _ => 0) (fun _ _ => none) (fun _ => ()) ℓ.uL ℓ.uH ℓ.wt ℓ.seat H.mgGains PFullK
    (14 * (2 * g + 1) + 4) (k5_at_full g hg) H.next ℓ.smpR (fun i => H.owes.low0 _ (H.owes.sent i)) ℓ.lk ℓ.Lk ℓ.same ℓ.blk ℓ.claimC ℓ.nm ℓ.Hd ℓ.bsW ℓ.dP ℓ.body ℓ.Zof H.owes
    H.rounds ℓ.hS ℓ.kr H.book H.plan H.asks H.readsOpen H.rowsApart H.riders ℓ.B H.seatOf H.runs Ee hEe Rch H.pubIs
    (A.facts5 D Dn.codes ((congrArg (·.shape) H.dataSent.d3).trans rfl) ((congrArg (·.layout) H.dataSent.d3).trans rfl) rfl)
    (hbare_of_reached D.N Mg LFullK PFullK (fun u => u) Rch H.place (k5_at_full g hg) (A.bare g hg))
    (hleft_of_reached D.N Mg LFullK PFullK (fun u => u) Rch H.place (k5_at_full g hg) (A.left g hg))
    H.doors H.doors' H.openBehind hs

end

end H2K5.Door

#print axioms H2K5.Door.k5_tiedAtR_left
