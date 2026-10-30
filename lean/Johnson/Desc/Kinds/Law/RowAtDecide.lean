-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/RowAtDecide.lean: THE OUTPUT HEAD's ROW OF THE TABLE OF JOINTS, ALL BUT THE 17 ROW FORMS, FROM THE BLOCK's OWN DECISION: STATED AND
PROVED, general in the seat. Law/RowHalf.lean's law speaks of Head.lean's hear; here it is said of
(kind cl L link piece p).decide: the decision of the block that runs (HeadKind.lean), at any carried record.
  decide_hears    where the block's decision goes on: given returns; hear returns at the record's ledger and ALL the rounds
                  shown, with none left; the ledger and what was heard are laid. (decideBy_spec, Law/Keeps.lean, with
                  "none left", which the decision tests under the name "the hearing uses the rounds up".)
  SeatBack        A NAMED PREMISE ON THE SEAT, at a record: behind the three layings OF WHAT THE BLOCK's HEARING RETURNED (at the
                  record's letters and ledger, WellLaid, on canonical rounds) the seat reads back the ledger that was
                  laid, WHAT WAS HEARD AS IT WAS LAID, the same letters (given) and the same points of the lookup. WHO
                  PAYS IT: the seat's files (Law/HeardBack.lean); NOT PAID HERE. Of any
                  ledger and heard record it would be false at the real seat.
  Opened, Closed  the row's items as sentences on a record through the seat's readers alone, the cells and the mask row:
                  Opened: at the letters and at what the record holds as heard, reads in truth: all 35 forms worth 0 at the
                  record's ledger, and the claim on the weights true. Closed: the two plain sums; each call's key vector's
                  worth; the two guests' sums.
  RowAtDecideStatement   the decision goes on from s to s' · SeatBack · the ledger in front WellLaid · the tests on the plan and
                  the request · y < V · the rounds canonical · no bad draw under the block's rule by name, at the ledger in
                  front: Opened at s' gives Closed at s'.
THE RULE IS blockRule c mask (L.ledger s) AT THE LETTERS THAT given RETURNS AT s: a function of the record in front, the cells and the
mask row: the form that the bridge to a block's errors asks ("rule a d").
WHAT IT DOES NOT SAY. c AND mask ARE LETTERS UNDER "FOR ALL", TIED HERE TO NOTHING THAT IS FIXED IN FRONT OF THE DRAWS: the law is meant to be spent at the
witness's components that are pinned in front of the block's first draw (the table of joints: pin 4 0, pinW): THAT INSTANCE IS THE CALLER's, AND IS NOWHERE; whoever
may pick mask behind the draws makes every hidden scalar what they like. rs IS WHAT decide IS SHOWN (no sealed digest): that these are the rounds of the written reading is another file's equation (Johnson/Desc/Sound/ShownRounds.lean).

-/
import Mathlib
import Johnson.Desc.Kinds.Law.RowHalf
import Johnson.Desc.Kinds.Law.GivenLetters
import Johnson.Desc.Kinds.HeadKind

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

namespace VerifiableInference.Desc.Kinds.Head.Law

open OnBytes (E)
open OnBytes.Model (Fork World)
open OnBytes.PscRun (Later)
open Norm (lt ls d lPd S2 T)

variable {S : Type}

/-- **A premise on the seat**: behind the three layings OF WHAT THE BLOCK's HEARING RETURNED it reads back what was laid,
and the same letters. (Of any ledger and any heard record it would be false at the real seat, which keeps of a heard
record only what a hearing can return.) -/
def SeatBack (p : Par) (L : Seat S) (s : S) : Prop :=
  ∀ (g : Given) (rs left : List Fmt.RoundView) (F : Fork) (H : HeardAll) (w : SumOnMatrix) (s1 s2 : S),
    given p L s = .ok g → WellLaid (L.ledger s) → Canonical rs →
    hear (L.ledger s) rs = some (H, F, left) →
    L.setLedger s F = .ok s1 → L.setHeard s1 H = .ok s2 →
    L.ledger (L.setWeightClaim s2 w) = F ∧ L.heard (L.setWeightClaim s2 w) = some H ∧
      given p L (L.setWeightClaim s2 w) = given p L s ∧
      L.lookup (L.setWeightClaim s2 w) = L.lookup s

/-- What the block opens, at letters g, what was heard H, a ledger G, the cells and the mask row. -/
def OpenedAt (g : Given) (H : HeardAll) (G : Fork) (c : NCells) (mask : Nat → E) : Prop :=
  let _ : Norm.Heard := H.1
  let _ : FinalNorm.Heard := H.2.1
  let _ : Heard := H.2.2
  let _ : FinalNorm.Reads := normReadsAtCells c
  let _ : Reads := readsAt c.toCells
  WeightTrue c.toCells G mask noEnt ∧
    ∀ name fs, claims.lookup name = some fs → ∀ f, f ∈ fs → atWorld G mask noEnt f = 0

/-- What it closes, but for the 17 row forms. zk: the calls' key points. -/
def ClosedAt (g : Given) (H : HeardAll) (G : Fork) (zk : Nat → Point) (c : NCells) (mask : Nat → E) :
    Prop :=
  let _ : Norm.Heard := H.1
  let _ : FinalNorm.Heard := H.2.1
  let _ : Heard := H.2.2
  let _ : FinalNorm.Reads := normReadsAtCells c
  let _ : Reads := readsAt c.toCells
  (meanAt c.toCells = 0 ∧ countAt c.toCells = 0) ∧
  (∀ call, call < 6 →
    rd (atWorld G mask noEnt (keyVector key (g.calls.getD call (0, [])).1 (callKeys call)))
      = (Finset.range (2 ^ (zk call).size)).sum fun i =>
          rd (eq (zk call) i) * rd (keyTable c call (i / T) (i % T))) ∧
  (∑ t < T, eq FinalNorm.zt t * clipAt c.toCells (corner 0 t)) = 0 ∧
  (∑ t < T, eq FinalNorm.zt t * tableAt c.toCells (corner 0 t)) = 0

/-- The same as sentences on a record, through the seat's readers alone. -/
def Opened (p : Par) (L : Seat S) (s : S) (c : NCells) (mask : Nat → E) : Prop :=
  ∃ g H, given p L s = .ok g ∧ L.heard s = some H ∧ OpenedAt g H (L.ledger s) c mask

@[inherit_doc Opened] def Closed (p : Par) (L : Seat S) (s : S) (c : NCells) (mask : Nat → E) : Prop :=
  ∃ g H z, given p L s = .ok g ∧ L.heard s = some H ∧ L.lookup s = some z ∧
    ClosedAt g H (L.ledger s) z.2 c mask

/-- The block's rule at a record in front: at the letters that given returns there; empty where it refuses. -/
noncomputable def ruleAt (p : Par) (L : Seat S) (s : S) (c : NCells) (mask : Nat → E) :
    List Fmt.RoundView → List E :=
  match given p L s with
  | .ok g => Came.blockRule c mask (L.ledger s)
  | .error _ => fun _ => []

/-- **THE ROW, ALL BUT THE 17 ROW FORMS, FROM THE BLOCK's DECISION.** -/
def RowAtDecideStatement : Prop :=
  ∀ (S Cl : Type) (cl : Form → Cl) (L : Seat S) (link piece : Nat) (p : Par) (s : S)
    (c : NCells) (mask : Nat → E) (s' : S) (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64))),
    (kind cl L link piece p).decide s rs gs = .ok s' → SeatBack p L s → WellLaid (L.ledger s) →
    p.ok = true → p.okStart (L.request s) = true →
    (∀ y, Reply.token L.toSeat s = some y → y < p.sizes.V) →
    Canonical rs → NoBad (ruleAt p L s c mask) rs →
    Opened p L s' c mask → Closed p L s' c mask

namespace Came

/-- Where the block's decision goes on. -/
theorem decide_hears {rounds : Given → List Round} {hear : Given → Hear HeardAll}
    {weights : Given → Behind → SumOnMatrix} {p : Par} {L : Seat S} {s s' : S}
    {rs : List Fmt.RoundView} (h : decideBy rounds hear weights p L s rs = .ok s') :
    ∃ (g : Given) (H : HeardAll) (F : Fork) (w : SumOnMatrix) (s1 s2 : S),
      given p L s = .ok g ∧ hear g (L.ledger s) rs = some (H, F, []) ∧
      L.setLedger s F = .ok s1 ∧ L.setHeard s1 H = .ok s2 ∧ s' = L.setWeightClaim s2 w := by
  unfold decideBy at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  split at h
  · simp at h
  · rename_i g hg
    split at h
    · simp at h
    · split at h
      · simp at h
      · rename_i v hv
        obtain ⟨H, F, left⟩ := v
        split at h
        · simp at h
        · rename_i u hu
          have hl : left = [] := by
            unfold need at hu
            split at hu
            · rename_i hb
              exact List.isEmpty_iff.1 hb
            · simp at hu
          subst hl
          split at h
          · simp at h
          · rename_i s1 h1
            split at h
            · simp at h
            · rename_i s2 h2
              simp only [Except.ok.injEq] at h
              refine ⟨g, H, F, _, s1, s2, hg, ?_, h1, h2, h.symm⟩
              unfold named at hv
              split at hv
              · rename_i y hy
                simp only [Except.ok.injEq] at hv
                rw [← hv]; exact hy
              · simp at hv

theorem rowAtDecide : RowAtDecideStatement := by
  intro S Cl cl L link piece p s c mask s' rs gs hd hback hWL hplan hreq hy hcan hnb hopen
  have hd' : decideBy (fun _ => rounds) (fun _ => hear) (fun _ _ => forTheMerge) p L s rs
      = .ok s' := hd
  obtain ⟨g, H, F1, w, s1, s2, hg, hh, e1, e2, rfl⟩ := decide_hears hd'
  obtain ⟨bL, bH, bG, bZ⟩ := hback g rs [] F1 H w s1 s2 hg hWL hcan hh e1 e2
  obtain ⟨g', H', hg', hH', hO⟩ := hopen
  rw [bG, hg] at hg'
  obtain rfl : g = g' := Except.ok.inj hg'
  rw [bH] at hH'
  obtain rfl : H = H' := Option.some.inj hH'
  rw [bL] at hO
  have hnb' : NoBad (blockRule c mask (L.ledger s)) rs := by
    unfold ruleAt at hnb
    rw [hg] at hnb
    exact hnb
  obtain ⟨z, y, hz, hty, hP, rfl⟩ := given_ok p L s g hg
  refine ⟨_, H, z, bG.trans hg, bH, bZ.trans hz, ?_⟩
  rw [bL]
  exact @rowHalf p.sizes p.policy (L.request s) ⟨y⟩ (@fromLookup p.sizes p.floor z.1 z.2).norm
    (@fromLookup p.sizes p.floor z.1 z.2).head p.sT p.floor z.1 z.2 c mask (L.ledger s) hplan hreq
    (hy y hty) hWL hP rfl rfl rs H F1 F1 hcan hh (Later.refl _) hnb' hO.1 hO.2

end Came

end VerifiableInference.Desc.Kinds.Head.Law

#print axioms VerifiableInference.Desc.Kinds.Head.Law.Came.decide_hears
#print axioms VerifiableInference.Desc.Kinds.Head.Law.Came.rowAtDecide
