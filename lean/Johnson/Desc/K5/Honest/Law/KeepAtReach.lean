-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K5/Honest/Law/KeepAtReach.lean: CONDITIONAL, under the library's one head on the public
input (`P5J.AtMgA`, Johnson/P5J/MgAtAll.lean): at every state that the first chain's own
sub-protocols reach in an attention segment in front of the block of the own rounds (number
14 (2 g + 1) + 4 of the flat list) and in front of the sending behind it (+ 5), five values of the
smallness test's part of the state are the plan's, with no draw counted: the library's own tuple
`K8.Ready.keep` (Johnson/Desc/First/K8/LawReadyRow.lean): the number of matrices, the matrices, the
number of combinations, the drawn matrix's entries, the count of draws.

Why. The library's law on the smallness test's draw at an attention segment
(Johnson/Desc/First/K8/LawReadyAtt.lean) asks six facts on the part tl0 that the segment's opening
laid, and that the blocks in front leave `keep`. Here `keep` is had as a term at the two borders.

THE COUNT OF DRAWS IS 0, NOT THE PLAN's OWN FIELD: the opening lays the plan's part WITH the list of
tables open and the count of draws 0 (`attFirstQuiet`).

How. The library walks this road, by position, along the raw flat list, for four other values
(Johnson/Desc/AtSeats/TlAtRch.lean); Johnson/Desc/K5/Honest/Law/TlOpen.lean walks it for four more.
ALL BUT THE SECTIONS "What is carried" AND "The opening" AND THE LAST TWO THEOREMS IS THAT TEXT ONCE
MORE, with the carried values exchanged, AND ONE TRUE DIFFERENCE: the lookup ON THE DIGITS counts
its draw in one of the five values, so its lemma on what it lays is struck, and the three lemmas on
the lookup's sub-protocol take a premise hpc: the address is not the digits'. At the lookup on the
calls, which alone stands in front of the own rounds, hpc holds by the two texts (its piece is 2,
the digits' 7 or 8). Over the block of the own rounds: `leavesFront_k5AtN`
(Johnson/Desc/K5/Honest/Law/Leaves.lean). THE WALK NOW STANDS THREE TIMES IN THE LIBRARY: a form
general in the carried values would hold all three; it is not typed.

Main names (all but the last two in the namespace H2K5.Honest.TlKeep):
  `att4`, `A4`: the values, and "they stay". `OpenAt`: what is carried.
  `tl_behind_first`, `tl_behind_look`: behind the segment's first place; behind the lookup on the
    calls.
  `keep_at_k5`, `keep_at_reach`: **the tuple at 14 (2 g + 1) + 4 and at + 5.**

Limits. The head is a hypothesis. Nothing on the plan's own numbers (that its drawn matrix's entries
are none, that its number of matrices is its list's length: the second is `hNM_of_plan`,
Johnson/Desc/K5/Honest/Law/PlanShp.lean). Where no state is reached the theorems say nothing. At the
function `OnBytes.secondHashFunction`, of which nothing is asked here; at the library's full size alone.
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.AtSeats.TlAtRch
import Johnson.Desc.K5.Honest.Law.DoorAtHead
import Johnson.Desc.K5.Honest.Law.Leaves
import Johnson.H2K5R.LawAtEntry

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace H2K5.Honest.TlKeep
open OnBytes OnBytes.Model OnBytes.Params Desc.Plain
open VerifiableInference.Desc
open VerifiableInference.Desc.First
open VerifiableInference.Desc.Keeps (Whole Decides Fn FnCl)
open Johnson.Desc.First.Walk
open Meaning.K2 (bindE unmarked_eq quiet_unmarked blockVia_whole withCaller_whole whole_same
  whole_sub guarded_whole mem_of_mapM_ok)

variable {Cl : Type}

/-! ## The relation -/

/-- Five values of the smallness test's part, and the frame's link's number, inside an attention
link; none elsewhere. -/
def att4 (s : S) :=
  match s.here with
  | .att a =>
    some (a.tl.NM, a.tl.mats, a.tl.tau, a.tl.cfF, a.tl.foldDrawn, a.L.check.frame.link)
  | _ => none

/-- **The five values stay.** -/
def A4 (s s' : S) : Prop := att4 s' = att4 s

theorem a4_refl (s : S) : A4 s s := rfl

theorem a4_trans (a b c : S) (h : A4 a b) (k : A4 b c) : A4 a c := Eq.trans k h

theorem a4_here {s s' : S} (h : s'.here = s.here) : A4 s s' := by
  unfold A4 att4
  rw [h]

/-! ## Writers of the state -/

theorem a4_mark (s : S) (name : String) : A4 s (s.mark name) := by
  unfold S.mark
  split
  · exact a4_refl s
  · exact a4_here rfl

theorem a4_putFork (s : S) (F : Fork) : A4 s (s.putFork F) := by
  unfold S.putFork
  repeat' split
  all_goals first
    | exact a4_refl _
    | exact a4_mark _ _
    | (unfold A4 att4; simp [*])

theorem a4_hearLook (s : S) (g : Forest.Heard) : A4 s (s.hearLook g) := by
  unfold S.hearLook
  repeat' split
  all_goals first
    | exact a4_refl _
    | exact a4_mark _ _
    | (unfold A4 att4; simp [*])

/-- Parameters with the state's own five values laid in their place. -/
theorem a4_putTl (s : S) (tl tl' : HTailF2) (h : s.tl? = some tl) (e1 : tl'.NM = tl.NM)
    (e2 : tl'.mats = tl.mats) (e3 : tl'.tau = tl.tau) (e4 : tl'.cfF = tl.cfF)
    (e5 : tl'.foldDrawn = tl.foldDrawn) : A4 s (s.putTl tl') := by
  unfold S.putTl
  cases ha : s.here with
  | att a =>
    have e : a.tl = tl := by
      unfold S.tl? at h
      rw [ha] at h
      exact Option.some.inj h
    unfold A4 att4
    simp [ha, e, e1, e2, e3, e4, e5]
  | head a => by_cases ho : a.opened = true <;> (unfold A4 att4; simp [ha, ho])
  | lay a => unfold A4 att4; simp [ha]
  | between => unfold A4 att4; simp [ha]
  | fin a => unfold A4 att4; simp [ha]
  | mem a => unfold A4 att4; simp [ha]

/-! ## The lookup -/

theorem seatCalls_put_a4 (claim : Aff → Cl) (s : S) (g : Forest.Heard) (G : Fork) :
    A4 s ((K3.seatCalls claim).put s g G) :=
  a4_trans _ _ _ (a4_putFork s G) (a4_hearLook _ g)

theorem seatCalls_mark_a4 (claim : Aff → Cl) (s : S) (G : Fork) :
    A4 s ((K3.seatCalls claim).mark s G) := a4_putFork s G

theorem seatDigits_mark_a4 (claim : Aff → Cl) (s : S) (G : Fork) :
    A4 s ((K3.seatDigits claim).mark s G) := a4_putFork s G

theorem quietLook_a4 (fs : Forest.Shape) : Fn A4 (K3.quietLook fs) := fun s s' h => by
  unfold K3.quietLook at h
  obtain ⟨_, _, h⟩ := bindE h
  obtain ⟨_, _, h⟩ := bindE h
  cases h
  exact a4_refl s

theorem quietDigits_a4 (used claims : Nat) : Fn A4 (K3.quietDigits used claims) :=
  fun s s' h => by
  unfold K3.quietDigits at h
  obtain ⟨_, _, h⟩ := bindE h
  obtain ⟨G, _, h⟩ := bindE h
  cases h
  exact a4_putFork s G

theorem quietHead_a4 (X : Verify.Public) : Fn A4 (K3.quietHead X) := fun s s' h => by
  unfold K3.quietHead at h
  split at h
  · rename_i a ha
    obtain ⟨_, _, h⟩ := bindE h
    obtain ⟨_, _, h⟩ := bindE h
    obtain ⟨_, _, h⟩ := bindE h
    obtain ⟨_, _, h⟩ := bindE h
    obtain ⟨_, _, h⟩ := bindE h
    obtain ⟨_, _, h⟩ := bindE h
    cases h
    unfold A4 att4
    simp [ha]
  · cases h

theorem quietAt_a4 (X : Verify.Public) (i : Nat) (digits : Bool)
    {f : S → Except String S} (h : K3.quietAt X i digits = some f) : Fn A4 f := by
  unfold K3.quietAt at h
  simp only at h
  repeat' split at h
  all_goals first
    | (cases h; exact quietHead_a4 X)
    | (cases h; exact quietLook_a4 _)
    | (obtain ⟨_, _, rfl⟩ := Option.map_eq_some_iff.1 h; exact quietDigits_a4 _ _)
    | cases h

/-- At an address that is not the lookup's on the digits (hpc): that lookup counts its draw in one
of the five values. -/
theorem theOwn_a4 (claim : Aff → Cl) (runs : Bool) (X : Verify.Public) (codes : Codes)
    (shape : ReqShape) (a : Place) (hpc : ∀ i, a.piece ≠ K3.pieceAt X i true) {b : Block S Cl}
    (h : K3.theOwn claim runs X codes shape a = some b) : Whole A4 b := by
  unfold K3.theOwn at h
  split at h
  · cases h
  · obtain ⟨i, _, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨digits, _, h⟩ := List.exists_of_findSome?_eq_some h
    split at h
    · cases h
    · rename_i hpiece
      obtain ⟨p, _, h⟩ := Option.bind_eq_some_iff.1 h
      obtain ⟨sent, _, h⟩ := Option.bind_eq_some_iff.1 h
      obtain ⟨laid, _, h⟩ := Option.bind_eq_some_iff.1 h
      obtain ⟨key, _, h⟩ := Option.map_eq_some_iff.1 h
      have W : Whole A4 (K3.Law.blockVia (if digits = true then K3.seatDigits claim
          else K3.seatCalls claim) a.piece laid sent p []) := by
        cases digits
        · exact blockVia_whole A4 a4_refl _ (seatCalls_put_a4 claim) (seatCalls_mark_a4 claim)
            _ _ _ _ _
        · exact absurd (by simpa using hpiece) (hpc i)
      rw [← h]
      cases runs
      · exact whole_same W rfl (fun _ hx => nomatch hx) rfl
      · exact whole_same W rfl (fun _ hx => hx) rfl

theorem theWhole_a4 (claim : Aff → Cl) (runs : Bool) (X : Verify.Public) (codes : Codes)
    (shape : ReqShape) (a : Place) (hpc : ∀ i, a.piece ≠ K3.pieceAt X i true) {b : Block S Cl}
    (h : K3.theWhole claim runs X codes shape a = some b) : Whole A4 b := by
  unfold K3.theWhole at h
  obtain ⟨b₀, h0, rfl⟩ := Option.map_eq_some_iff.1 h
  have W := theOwn_a4 claim runs X codes shape a hpc h0
  split
  · rename_i f hf
    obtain ⟨i, _, hq⟩ := Option.bind_eq_some_iff.1 hf
    exact Keeps.andThen_whole A4 a4_trans _ _ _ W
      ⟨Keeps.quiet_decides A4 _ _ _ _ f (quietAt_a4 X i _ hq), (fun _ hc => nomatch hc),
        (fun _ hc => nomatch hc)⟩
  · exact W

/-- **The lookup's sub-protocol at an address that is not the digits'.** -/
theorem theStated_a4 (claim : Aff → Cl) (readers : Nat → Option (K3.Readers S))
    (X : Verify.Public) (codes : Codes) (shape : ReqShape) (a : Place)
    (hpc : ∀ i, a.piece ≠ K3.pieceAt X i true) {b : Block S Cl}
    (h : K3.theStated claim readers X codes shape a = some b) : Whole A4 b := by
  unfold K3.theStated at h
  obtain ⟨b₀, h0, h⟩ := Option.bind_eq_some_iff.1 h
  have W := theWhole_a4 claim true X codes shape a hpc h0
  split at h
  · cases h
    exact W
  · split at h
    · cases h
      exact W
    · split at h
      · cases h
        exact W
      · obtain ⟨p, -, rfl⟩ := Option.map_eq_some_iff.1 h
        exact withCaller_whole A4 _ (seatCalls_mark_a4 claim) p _ W

/-! ## What is carried -/

/-- In an attention link number l: the number of matrices, the matrices, the number of combinations
and the drawn matrix's entries are t₀'s; no draw is counted. -/
def OpenAt (t₀ : HTailF2) (l : ℕ) (s : S) : Prop :=
  ∃ a₀, s.here = .att a₀ ∧ a₀.tl.NM = t₀.NM ∧ a₀.tl.mats = t₀.mats ∧ a₀.tl.tau = t₀.tau ∧
    a₀.tl.cfF = t₀.cfF ∧ a₀.tl.foldDrawn = 0 ∧ a₀.L.check.frame.link = l

theorem OpenAt.carry {t₀ : HTailF2} {l : ℕ} {s s' : S} (k : OpenAt t₀ l s) (h : A4 s s') :
    OpenAt t₀ l s' := by
  obtain ⟨a₀, e, k1, k2, k3, k4, k5, el⟩ := k
  unfold A4 att4 at h
  rw [e] at h
  dsimp only at h
  cases e' : s'.here with
  | att a' =>
    rw [e'] at h
    dsimp only at h
    have h0 := Option.some.inj h
    simp only [Prod.mk.injEq] at h0
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h0
    exact ⟨a', e', h1.trans k1, h2.trans k2, h3.trans k3, h4.trans k4, h5.trans k5, h6.trans el⟩
  | _ =>
    rw [e'] at h
    cases h

/-! ## The opening -/

/-- Behind an attention link's "opened". -/
theorem openAtt_lays (P : AttPar) (s t : S) (h : openAtt P s = .ok t) : OpenAt P.tl₀ P.l t := by
  obtain ⟨hB, _, _, hlk, hL, _⟩ := Law.openAtt_ok h
  unfold openAtt at h
  obtain ⟨-, -, h⟩ := bindE h
  obtain ⟨-, -, h⟩ := bindE h
  obtain ⟨a, hq, h⟩ := bindE h
  have ht := unmarked_eq h
  have etl : a.tl = { P.tl₀ with funClosed := false, foldDrawn := 0 } := by
    unfold attFirstQuiet at hq
    split at hq
    · cases hq
    · split at hq
      · cases hq
      · cases hq
        rfl
  have hh : ∃ a₀, t.here = .att a₀ ∧ a₀.L = a.L ∧ a₀.tl = a.tl := by
    rw [ht]
    unfold S.enterAtt
    simp only [show ({ s with out := a.out } : S).atBetween = true from hB, if_true]
    exact ⟨_, rfl, rfl, rfl⟩
  obtain ⟨a₀, hh, eL, eT⟩ := hh
  refine ⟨a₀, hh, by rw [eT, etl], by rw [eT, etl], by rw [eT, etl], by rw [eT, etl],
    by rw [eT, etl], ?_⟩
  have h2 : t.link? = some a₀.L := by
    unfold S.link?
    rw [hh]
  have e3 := Option.some.inj (h2.symm.trans hL)
  rw [e3]
  exact hlk

/-! ## The walk -/

open Johnson.Desc.First.Walk.Tied (Reach RchAt rchAt_raw stepYes_decide)
open VerifiableInference.Desc.Sound (linksFull onQ Frame linkNo)
open IM (Open k1Ix)

section
variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S ProofFile.Cl)} {c : Chain S ProofFile.Cl}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat} {Q : Type} {start : Q → S}

/-- **Behind an attention link's first place**, with "opened" joined behind it. -/
theorem tl_behind_first (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (g : ℕ) (hg : g < 12) (a : Q × S)
    (h : Reach 0 c.blocksInOrder start (14 * (2 * g + 1) + 2 + 1) a) :
    ∃ Ap, Bs.G₀.W.A[g]? = some Ap ∧ OpenAt Ap.seam.tl (2 * g + 1) a.2 := by
  obtain ⟨fs, hfs, hh⟩ := IM.frames_sit hS hR O
  obtain ⟨f, _, k, _, b, b', _, hf, _, _, _, _, _, iB, hk, _, ep, hj, _, _, _⟩ :=
    hh (2 * g + 1) (by omega)
  obtain ⟨nam, -⟩ := IM.ground_named hS hR O.pub O.blank
  obtain ⟨_, X, _, _, _, _, hX, hkX, hgX, _⟩ := nam g hg
  obtain ⟨bX, hbX, ek, eg⟩ := VerifiableInference.Desc.K1.built_of_ground O.blank hX
  cases h with
  | @succ _ z s s' b₁ h1 hb₁ hy =>
    obtain rfl : b = b₁ := Option.some.inj (iB.symm.trans hb₁)
    obtain ⟨rs, gs, hd⟩ := stepYes_decide hy
    obtain ⟨fs', f', m, hfs', hf', d1, _, d2, _, _⟩ := hj.yes hd
    rcases IM.frames_arms hfs' (2 * g + 1) f' hf' with ⟨X2, h2, k2, _⟩ | ⟨l0, _⟩ |
      ⟨Pa, nLin, hfa, _, hop, _⟩ | ⟨Pa, hfa, _⟩
    · obtain rfl : bX = X2 := Option.some.inj (hbX.symm.trans h2)
      rw [ek, hkX] at k2
      cases k2
    · omega
    · unfold Seat.frameAt at hfa
      rw [hbX] at hfa
      simp only [Option.bind_eq_bind, Option.bind_some, ek, hkX, eg, hgX] at hfa
      rw [if_neg (by simp)] at hfa
      simp only [beq_self_eq_true, if_true] at hfa
      obtain ⟨p, hp, e⟩ := Option.bind_eq_some_iff.1 hfa
      have e' : Seat.Par.att { X := Seat.pubOf bX, l := 2 * g + 1, ns := p.ns, tl₀ := p.seam.tl }
          p.nLin = Seat.Par.att Pa nLin := Option.some.inj e
      injection e' with e1 _
      subst e1
      rw [hop] at d2
      exact ⟨p, by rw [O.W]; exact hp, openAtt_lays _ m s' d2⟩
    · unfold Seat.frameAt at hfa
      rw [hbX] at hfa
      simp only [Option.bind_eq_bind, Option.bind_some, ek, hkX, eg, hgX] at hfa
      rw [if_neg (by simp)] at hfa
      simp only [beq_self_eq_true, if_true] at hfa
      obtain ⟨p, _, e⟩ := Option.bind_eq_some_iff.1 hfa
      cases Option.some.inj e

/-- **Behind the lookup on the calls.** -/
theorem tl_behind_look (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (g : ℕ) (hg : g < 12) (a : Q × S)
    (h : Reach 0 c.blocksInOrder start (14 * (2 * g + 1) + 2 + 1 + 1) a) :
    ∃ Ap, Bs.G₀.W.A[g]? = some Ap ∧ OpenAt Ap.seam.tl (2 * g + 1) a.2 := by
  obtain ⟨Lk, b, b', e1, e2, h3, hla⟩ := IM.k3_of hS hR O (2 * g + 1) (by omega) false
  have iB := IM.hear_at_flat e1 e2
  rw [IM.flatIx_scope hS hR O (by omega) (IM.k3Ix (2 * g + 1) false)] at iB
  have hix : IM.k3Ix (2 * g + 1) false = 1 := by
    show (if false = true then 6 else 1) + (if 2 * g + 1 = 24 then 1 else 0) = 1
    rw [if_neg (by omega : ¬ 2 * g + 1 = 24)]
    rfl
  rw [hix] at iB
  cases h with
  | @succ _ z s s' b₁ h1 hb₁ hy =>
    obtain rfl : b = b₁ := Option.some.inj (iB.symm.trans (by
      rw [show 14 * (2 * g + 1) + 1 + 2 = 14 * (2 * g + 1) + 2 + 1 by omega]
      exact hb₁))
    obtain ⟨rs, gs, hd⟩ := stepYes_decide hy
    obtain ⟨Ap, hA, k⟩ := tl_behind_first hS hR O g hg (z, s) h1
    have hpc : ∀ i, (IM.k3Place (2 * g + 1) false).piece ≠ K3.pieceAt Bs.G₀.W i true := by
      intro i
      show IM.k3Ix (2 * g + 1) false + 1 ≠ _
      rw [hix]
      unfold K3.pieceAt
      split <;> simp
    exact ⟨Ap, hA, k.carry ((theStated_a4 _ _ _ _ _ _ hpc h3).1 _ _ _ _
      ((IM.yes_alone hla (fun e => nomatch e) s s' rs gs).1 hd).1)⟩


end

end H2K5.Honest.TlKeep

namespace H2K5.Honest
open OnBytes OnBytes.Model OnBytes.Maker
open VerifiableInference.Desc VerifiableInference.Desc.First
open Johnson.Desc.First.Walk.Tied (Reach)
open P5J (AtMgA TS)

/-- **The five values in front of the block of the own rounds.** Conditional: the head; hg; ea: the
group's plan; hr: the state is reached at number 14 (2 g + 1) + 4. -/
theorem keep_at_k5 {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
    {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl} {x : Look.Place}
    (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {g : ℕ} (hg : g < 12) {a : Attention.Plan}
    (ea : (P5J.At.X Zp).A[g]? = some a) {π : ProofFile.InstPub} {s : S}
    (hr : Reach 0 cF.blocksInOrder (ProofFile.startS Zp) (14 * (2 * g + 1) + 4) (π, s)) :
    K8.Ready.keep s =
      some (a.seam.tl.NM, a.seam.tl.mats, a.seam.tl.tau, a.seam.tl.cfF, 0) := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain ⟨Ap, hA, a₀, e₀, k1, k2, k3, k4, k5, _⟩ :=
    TlKeep.tl_behind_look h.scope h.reads O g hg (π, s) hr
  rw [O.W] at hA
  obtain rfl : Ap = a := Option.some.inj (hA.symm.trans ea)
  unfold K8.Ready.keep S.tl?
  rw [e₀]
  show some (a₀.tl.NM, a₀.tl.mats, a₀.tl.tau, a₀.tl.cfF, a₀.tl.foldDrawn) = _
  rw [k1, k2, k3, k4, k5]

/-- **THE FIVE VALUES IN FRONT OF THE SENDING BEHIND WHICH THE LIST OF TABLES IS CLOSED**: at every
state reached at number 14 (2 g + 1) + 5: the library's tuple `K8.Ready.keep` is the plan's, with no
draw counted. Conditional: the head; hg; ea; hr. -/
theorem keep_at_reach {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
    {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl} {x : Look.Place}
    (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {g : ℕ} (hg : g < 12) {a : Attention.Plan}
    (ea : (P5J.At.X Zp).A[g]? = some a) {π : ProofFile.InstPub} {s : S}
    (hr : Reach 0 cF.blocksInOrder (ProofFile.startS Zp) (14 * (2 * g + 1) + 5) (π, s)) :
    K8.Ready.keep s =
      some (a.seam.tl.NM, a.seam.tl.mats, a.seam.tl.tau, a.seam.tl.cfF, 0) := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain ⟨h4, g', hg', e⟩ := Att.P.att_only O.pub O.blank
    (IM.subs_att h.scope h.reads O.pub O.blank hg)
  obtain rfl : g' = g := by omega
  obtain ⟨Lk, Eb, b', e1, e2, hat, hla⟩ := Att.P.k5_alone O h4 hg'
  have e3 := IM.flatIx_scope h.scope h.reads O (l := 2 * g' + 1) (by omega) 2
  have hfl : cF.blocksInOrder[14 * (2 * g' + 1) + 4]? = some Eb := by
    have hfl0 := IM.hear_at_flat e1 e2
    rw [e3, show 14 * (2 * g' + 1) + 2 + 2 = 14 * (2 * g' + 1) + 4 by omega] at hfl0
    exact hfl0
  cases hr with
  | @succ _ z s0 s' b₁ h1 hb₁ hy =>
    obtain rfl : Eb = b₁ := Option.some.inj (hfl.symm.trans hb₁)
    obtain ⟨rs, gs, hd⟩ := Johnson.Desc.First.Walk.Tied.stepYes_decide hy
    have hd' := ((IM.yes_alone hla (fun e => nomatch e) s0 s rs gs).1 hd).1
    rw [(leavesFront_k5AtN hat).1 s0 rs gs s hd']
    exact keep_at_k5 h hg ea h1

end H2K5.Honest

#print axioms H2K5.Honest.TlKeep.a4_refl
#print axioms H2K5.Honest.TlKeep.a4_trans
#print axioms H2K5.Honest.TlKeep.a4_here
#print axioms H2K5.Honest.TlKeep.a4_mark
#print axioms H2K5.Honest.TlKeep.a4_putFork
#print axioms H2K5.Honest.TlKeep.a4_hearLook
#print axioms H2K5.Honest.TlKeep.a4_putTl
#print axioms H2K5.Honest.TlKeep.seatCalls_put_a4
#print axioms H2K5.Honest.TlKeep.seatCalls_mark_a4
#print axioms H2K5.Honest.TlKeep.seatDigits_mark_a4
#print axioms H2K5.Honest.TlKeep.quietLook_a4
#print axioms H2K5.Honest.TlKeep.quietDigits_a4
#print axioms H2K5.Honest.TlKeep.quietHead_a4
#print axioms H2K5.Honest.TlKeep.quietAt_a4
#print axioms H2K5.Honest.TlKeep.theOwn_a4
#print axioms H2K5.Honest.TlKeep.theWhole_a4
#print axioms H2K5.Honest.TlKeep.theStated_a4
#print axioms H2K5.Honest.TlKeep.OpenAt.carry
#print axioms H2K5.Honest.TlKeep.openAtt_lays
#print axioms H2K5.Honest.TlKeep.tl_behind_first
#print axioms H2K5.Honest.TlKeep.tl_behind_look
#print axioms H2K5.Honest.keep_at_k5
#print axioms H2K5.Honest.keep_at_reach
