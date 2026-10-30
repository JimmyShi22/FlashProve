-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Batch/Law/Row3.lean
(kind K9's soundness lemma): THEOREM: KIND K9's LEMMA IN THE FORM THAT THE RULE OF
COMPOSITION TAKES, WHOLE: three pieces in a row:
  the batching (L.batchB) · the runs behind the batching (the frame's block) · the one equation
  (K9.oneEquation X pw);
FROM  "all equations of the segment hold at the data that the witness's tables hold, and every open
      row of the segment's group holds on these tables"
TO    "every open row of the segment's group holds on the witness's tables".
  boundAt   the data to which the prover is bound, at a statement and a witness that meets the
            context: dataAt (the tables that the witness holds, read by the state's own layout,
            frame and statement).
  relAt     the four relations at the four boundaries. "Every open row holds" is carried backward
            past all three pieces: a block in front that has laid a row on the group finds it.
  goodIn_and   a claim carried beside a piece.
  k9_row    EachGoodIn on (relAt ..) j [pb, pq, pe].
It glues Law/RealPiece.lean (batch_goodIn_real), Johnson/Desc/LinkLaw3.lean (behind_goodIn) and
Law/DoorFacts.lean (equation_goodIn') by the rule of consequence (Johnson/Desc/LinkLaw7.lean).

**THE HYPOTHESIS THAT WEIGHS MOST: hpin: "ONE STATEMENT HAS ONE TABLE": two witnesses that both meet
the context ctx at a statement hold the same tables.** ctx is a letter, carried beside at all four
boundaries (hcb, hcq, hce): what the pieces read and leave; meant: the witness's tables are pinned
by the statement: they are what the oracles' strings AND the answers to the out-of-domain samples
decode to. Without such a context hpin fails where a proximity test accepts words within a radius
at which several codewords lie (list decoding): two witnesses could hold two tables. That a sample
picks just one member of the list, at which price, and that a closing concludes of that one
codeword, is another law's (the row words_are_committed): NONE OF IT IS SHOWN HERE. THE WEIGHT LIES
ON ctx: it stands in every relation, the last too: whoever stands behind the third piece (the
closing) must give it of its witness; at a context that no witness meets, all of this holds idly.

THE OTHER HYPOTHESES, BY NAME: H: the premises of the segment's law at semOf. THAT THE BATCHING IS
THE REAL BLOCK K9.batch X p ENTERS THROUGH H ALONE: Law/RealPiece.lean: premises_real pays "batch"
at L.batch = K9.batch X p; Law/MemberSeg.lean [not in this library] is a member of H, and of H alone: NO MEMBER MEETS ALL
HYPOTHESES OF k9_row TOGETHER YET · the three pieces hold the three blocks · their extractors hand
the witness on · the conditions on j .. j + 3 (ready; behind; handed on) · dataAt and "every open
row holds" are carried past the first two pieces (hdb, hdq, hgb, hgq: Law/Carry.lean pays them down
to the runs' duty) · the tables are the same in front of and behind the third (htab) · the lens · N
· inside · positions of at most 64 bits · no drawn element in the rounds put behind · the reading
one to one on typed elements (Law/Member.lean: paid at the library's reading) · the first piece's
errors. None is shown at a segment of the protocol.
GroupHoldsAt is a "for all": it holds idly where the lens gives nothing or the group is not there;
at the door the door's own test "the group is there" shuts that out (door_group).

-/
import Johnson.Desc.LinkLaw7
import Johnson.Desc.First.Batch.Law.RowFacts
import Johnson.Desc.First.Batch.Law.RealPiece

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K9L
open OnBytes OnBytes.Model OnBytes.Maker OnBytes.Flat KObj
open VerifiableInference.Desc.K9 (Lens Where batch)
open VerifiableInference.Desc.Sound
open _root_.Run (ckP EV toU3)
open _root_.Iop (Err)

variable {T P K W : Type} [Field K] [Fintype K] [DecidableEq K] {F : Frame}

/-- The data to which the prover is bound, at a witness that meets the context ctx (what the
pieces read and leave: for one, that the witness's tables are pinned by the statement). -/
def boundAt (X : Lens T) (tabOf : T × F.E.Str → W → Nat → OnBytes.Part → Nat → K)
    (ctx : T × F.E.Str → W → Prop) (a : T × F.E.Str) (w : W) (y : Bound K) : Prop :=
  ctx a w ∧ y = dataAt X a.1 (tabOf a w)

/-- The relations at the four boundaries j, j + 1, j + 2, j + 3 (and, beyond, the last). -/
def relAt (ρ : Reading K) (X : Lens T) (O : Others T P K) (L : Link T Claim) (N : Nat)
    (tabOf : T × F.E.Str → W → Nat → OnBytes.Part → Nat → K) (ctx : T × F.E.Str → W → Prop)
    (j : ℕ) : ℕ → T × F.E.Str → W → Prop := fun i a w =>
  if i = j then
    (∃ y, boundAt X tabOf ctx a w y ∧ (semOf ρ X O).AllEq L.hear ((semOf ρ X O).fixed a.1) y) ∧
      GroupHoldsAt X ρ N a.1 (tabOf a w)
  else if i = j + 1 then
    (∃ y, boundAt X tabOf ctx a w y ∧
      ∃ t, afterIn L.hear L.orderAfter a.1 = .ok t ∧ (semOf ρ X O).one t a.1 y = 0) ∧
      GroupHoldsAt X ρ N a.1 (tabOf a w)
  else if i = j + 2 then
    (oneK X ρ a.1 a.1 (dataAt X a.1 (tabOf a w)) = 0 ∧ GroupHoldsAt X ρ N a.1 (tabOf a w)) ∧
      ctx a w
  else GroupHoldsAt X ρ N a.1 (tabOf a w) ∧ ctx a w

omit [Field K] [Fintype K] [DecidableEq K] in
/-- A claim carried beside a piece. -/
theorem goodIn_and {S Cl : Type} {C : _root_.Run.PQ.CK} (p : Piece C F S Cl W)
    {on on' : S × F.E.Str → Prop} {R R' Q Q' : S × F.E.Str → W → Prop} (h : p.GoodIn on on' R R')
    (hQ : ∀ a τ b w, on a → p.ior.red.out a τ = some b → Q' b w → Q a (p.ext a τ w)) :
    p.GoodIn on on' (fun a w => R a w ∧ Q a w) (fun b w => R' b w ∧ Q' b w) := by
  intro a ha
  refine _root_.Iop.Doomed.mono _ _ ?_ (h a ha)
  intro τ hτ b hb
  obtain ⟨h1, h2⟩ := hτ b hb
  exact ⟨h1, fun w hw => ⟨h2 w hw.1, hQ a τ b w ha hb hw.2⟩⟩

/-- **Kind K9's three pieces in a row.** -/
theorem k9_row (ρ : Reading K) (X : Lens T) (O : Others T P K) (pw : Where) (L : Link T Claim)
    (d N j : ℕ) (H : (semOf ρ X O).Premises L F.ft d)
    (pb pq pe : Piece (ckP .two) F T Claim W)
    (hpb : pb.b = below L.batchB) (hpq : pq.b = below L.behindB)
    (hpe : pe.b = below (K9.oneEquation X pw))
    (hextb : ∀ a τ w, pb.ext a τ w = w) (hextq : ∀ a τ w, pq.ext a τ w = w)
    (hexte : ∀ a τ w, pe.ext a τ w = w)
    (on : ℕ → T × F.E.Str → Prop)
    (tabOf : T × F.E.Str → W → Nat → OnBytes.Part → Nat → K) (ctx : T × F.E.Str → W → Prop)
    (hready : ∀ a, on j a → (semOf ρ X O).ready a.1)
    (hbehind : ∀ a, on (j + 1) a → (semOf ρ X O).behind a.1)
    (hhb : ∀ a τ b, on j a → pb.ior.red.out a τ = some b → on (j + 1) b)
    (hhq : ∀ a τ b, on (j + 1) a → pq.ior.red.out a τ = some b → on (j + 2) b)
    (hhe : ∀ a τ b, on (j + 2) a → pe.ior.red.out a τ = some b → on (j + 3) b)
    (hpin : ∀ a w w', on j a → ctx a w → ctx a w' → tabOf a w = tabOf a w')
    (hcb : ∀ a τ b w, on j a → pb.ior.red.out a τ = some b → ctx b w → ctx a w)
    (hcq : ∀ a τ b w, on (j + 1) a → pq.ior.red.out a τ = some b → ctx b w → ctx a w)
    (hce : ∀ a τ b w, on (j + 2) a → pe.ior.red.out a τ = some b → ctx b w → ctx a w)
    (hdb : ∀ a τ b w, on j a → pb.ior.red.out a τ = some b →
      dataAt X b.1 (tabOf b w) = dataAt X a.1 (tabOf a w))
    (hdq : ∀ a τ b w, on (j + 1) a → pq.ior.red.out a τ = some b →
      dataAt X b.1 (tabOf b w) = dataAt X a.1 (tabOf a w))
    (hgb : ∀ a τ b w, on j a → pb.ior.red.out a τ = some b →
      GroupHoldsAt X ρ N b.1 (tabOf b w) → GroupHoldsAt X ρ N a.1 (tabOf a w))
    (hgq : ∀ a τ b w, on (j + 1) a → pq.ior.red.out a τ = some b →
      GroupHoldsAt X ρ N b.1 (tabOf b w) → GroupHoldsAt X ρ N a.1 (tabOf a w))
    (htab : ∀ a τ b w, on (j + 2) a → pe.ior.red.out a τ = some b → tabOf b w = tabOf a w)
    (lens : ∀ s a, (X.get? s).isSome = true →
      ∃ a', X.get? (X.set s a) = some a' ∧ a'.L = a.L ∧ a'.d.st = a.d.st)
    (hN : ∀ s, on (j + 2) s → ∀ a, X.get? s.1 = some a → a.d.st.oracles.size ≤ N)
    (inside : ∀ s, on (j + 2) s → ∀ a, X.get? s.1 = some a → ∀ born name r,
      reqArray a.L.check.rows.layout born name = some r → ∀ b ∈ r.blocks, Inside r b)
    (hlog : ∀ r ∈ pb.ds, r.entry.logN ≤ 64) (hback : ∀ r ∈ pb.back, r.drawn.elems = [])
    (hinj : Function.Injective fun a : EV .two => ρ.val (E.ofTriple (toU3 a)))
    (herr : Err.le (allErr (fun _ _ => d) 0 pb.ds) pb.err) :
    EachGoodIn on (relAt ρ X O L N tabOf ctx j) j [pb, pq, pe] := by
  have r0 : relAt ρ X O L N tabOf ctx j j = fun a w =>
      (∃ y, boundAt X tabOf ctx a w y ∧ (semOf ρ X O).AllEq L.hear ((semOf ρ X O).fixed a.1) y) ∧
        GroupHoldsAt X ρ N a.1 (tabOf a w) := by
    funext a w
    simp [relAt]
  have r1 : relAt ρ X O L N tabOf ctx j (j + 1) = fun a w => (∃ y, boundAt X tabOf ctx a w y ∧
      ∃ t, afterIn L.hear L.orderAfter a.1 = .ok t ∧ (semOf ρ X O).one t a.1 y = 0) ∧
        GroupHoldsAt X ρ N a.1 (tabOf a w) := by
    funext a w
    simp [relAt]
  have r2 : relAt ρ X O L N tabOf ctx j (j + 1 + 1) = fun a w =>
      (oneK X ρ a.1 a.1 (dataAt X a.1 (tabOf a w)) = 0 ∧ GroupHoldsAt X ρ N a.1 (tabOf a w)) ∧
        ctx a w := by
    funext a w
    unfold relAt
    rw [if_neg (by omega), if_neg (by omega), if_pos (by omega)]
  have r3 : relAt ρ X O L N tabOf ctx j (j + 1 + 1 + 1) = fun a w =>
      GroupHoldsAt X ρ N a.1 (tabOf a w) ∧ ctx a w := by
    funext a w
    unfold relAt
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
  refine ⟨?_, ?_, ?_, trivial⟩
  · rw [r0, r1]
    exact goodIn_and pb (batch_goodIn_real ρ X O L d H pb hpb hextb (on j) (on (j + 1))
      (boundAt X tabOf ctx) hready hhb (fun a w w' y y' ha h1 h2 => by
        rw [h1.2, h2.2, hpin a w w' ha h1.1 h2.1])
      (fun a τ b w y ha hout hB => ⟨hcb a τ b w ha hout hB.1, by
        rw [hB.2]
        exact hdb a τ b w ha hout⟩)
      hlog hback hinj herr) (fun a τ b w ha hout hq => by
        rw [hextb]
        exact hgb a τ b w ha hout hq)
  · rw [r1, r2]
    refine goodIn_conseq pq (goodIn_and pq (behind_goodIn (semOf ρ X O) L H.later H.after pq hpq
      hextq (on (j + 1)) (on (j + 1 + 1)) (boundAt X tabOf ctx) hbehind hhq
      (fun a τ b w y ha hout hB => ⟨hcq a τ b w ha hout hB.1, by
        rw [hB.2]
        exact hdq a τ b w ha hout⟩)) (fun a τ b w ha hout hq => by
        rw [hextq]
        exact hgq a τ b w ha hout hq))
      (fun _ h => h) (fun _ h => h) (fun _ _ _ h => h)
      (fun b w _ h => ⟨⟨_, ⟨h.2, rfl⟩, h.1.1⟩, h.1.2⟩)
  · rw [r2, r3]
    exact goodIn_and pe (equation_goodIn' X ρ pw N pe hpe hexte (on (j + 1 + 1))
      (on (j + 1 + 1 + 1)) tabOf hhe htab lens hN inside) (fun a τ b w ha hout hq => by
        rw [hexte]
        exact hce a τ b w ha hout hq)

end VerifiableInference.Desc.K9L

#print axioms VerifiableInference.Desc.K9L.k9_row
