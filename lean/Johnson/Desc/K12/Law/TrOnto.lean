-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
import Johnson.Desc.K12.Law.DrawnOnto
import Johnson.Top.H0.StepLaws.StepLaws
/-
Johnson/Desc/K12/Law/TrOnto.lean: A TYPED TRANSCRIPT FOR GIVEN ROUNDS: for every list of written rounds' data, every list of rounds as a view shows them that fit these data (RoundIs), and every choice of written oracles, there is a typed transcript (challenges: hash blocks) that shows just these rounds, their sealed digests apart, holds just these oracles, and passes all tests of work. NO SOUNDNESS IS CLAIMED. NOTHING ON HIDING.
  plain_onto     items as shown whose kinds are the round's, the roots apart, are PQ.PlainOf.gots of some plain part
  RoundIs d r    the items' kinds · logN ≤ 64 · DrawnIs d.entry d.kind r.drawn (Johnson/Desc/K12/Law/DrawnOnto.lean)
  Orcs · orcsOf  one written oracle a round; those of a transcript
  tr_onto        Forall₂ RoundIs ds rs ⇒ ∀ os, ∃ τ, (rvSL ds τ).map noDigest = rs.map noDigest ∧ passSL ds (rhoSL ds τ) = true ∧ orcsOf ds τ = os
  tr_with        a transcript with any written oracles: no premise (for whoever has tables in hand and wants a carrier)
  step_noDigest · step_congr   Block.step reads its rounds without the sealed digest: two lists of rounds that are one without it give one verdict
WHAT IT DOES NOT SAY: that the blocks are a hash function's answers, or that the bits of work came from a search (THEY ARE LAID AS ZEROS: GChal.zero: SO THE TESTS OF WORK PASS: a yes at such a transcript says nothing of a search): the transcript is any member of the game's type: the statement lives in the oracle model.
EVERY THEOREM OF THIS FILE IS PROVED OUTRIGHT: nothing is left open and nothing is laid down by decree; what each rests on is printed at the file's end.
-/
set_option autoImplicit false
namespace H2K.Onto
open Run Iop OnBytes.Slice VerifiableInference.Desc

theorem plain_onto : ∀ (l : List Fmt.Item) (g : List Fmt.ItemValue),
    g.map itemOf = l.filter (· != .root) → ∃ x : PQ.PlainOf l, PQ.PlainOf.gots l x = g
  | [], [], _ => ⟨(), rfl⟩
  | [], _ :: _, h => nomatch h
  | .root :: l, g, h => plain_onto l g h
  | .f :: l, [], h => nomatch h
  | .f :: l, .f a :: g, h => by
    obtain ⟨x, hx⟩ := plain_onto l g (List.cons.inj h).2
    exact ⟨((a, x) : UInt64 × PQ.PlainOf l), congrArg (Fmt.ItemValue.f a :: ·) hx⟩
  | .f :: l, .e _ :: g, h => nomatch (List.cons.inj h).1
  | .f :: l, .word _ :: g, h => nomatch (List.cons.inj h).1
  | .f :: l, .root _ :: g, h => nomatch (List.cons.inj h).1
  | .f :: l, .answer _ :: g, h => nomatch (List.cons.inj h).1
  | .word :: l, [], h => nomatch h
  | .word :: l, .word a :: g, h => by
    obtain ⟨x, hx⟩ := plain_onto l g (List.cons.inj h).2
    exact ⟨((a, x) : UInt64 × PQ.PlainOf l), congrArg (Fmt.ItemValue.word a :: ·) hx⟩
  | .word :: l, .e _ :: g, h => nomatch (List.cons.inj h).1
  | .word :: l, .f _ :: g, h => nomatch (List.cons.inj h).1
  | .word :: l, .root _ :: g, h => nomatch (List.cons.inj h).1
  | .word :: l, .answer _ :: g, h => nomatch (List.cons.inj h).1
  | .e :: l, [], h => nomatch h
  | .e :: l, .e a :: g, h => by
    obtain ⟨x, hx⟩ := plain_onto l g (List.cons.inj h).2
    exact ⟨((a, x) : Fmt.Ext × PQ.PlainOf l), congrArg (Fmt.ItemValue.e a :: ·) hx⟩
  | .e :: l, .f _ :: g, h => nomatch (List.cons.inj h).1
  | .e :: l, .word _ :: g, h => nomatch (List.cons.inj h).1
  | .e :: l, .root _ :: g, h => nomatch (List.cons.inj h).1
  | .e :: l, .answer _ :: g, h => nomatch (List.cons.inj h).1
  | .answer :: l, [], h => nomatch h
  | .answer :: l, .answer a :: g, h => by
    obtain ⟨x, hx⟩ := plain_onto l g (List.cons.inj h).2
    exact ⟨((a, x) : Fmt.Ext × PQ.PlainOf l), congrArg (Fmt.ItemValue.answer a :: ·) hx⟩
  | .answer :: l, .f _ :: g, h => nomatch (List.cons.inj h).1
  | .answer :: l, .word _ :: g, h => nomatch (List.cons.inj h).1
  | .answer :: l, .root _ :: g, h => nomatch (List.cons.inj h).1
  | .answer :: l, .e _ :: g, h => nomatch (List.cons.inj h).1

/-- A round as a view shows it fits a written round's data. -/
structure RoundIs (d : PQ.RD) (r : Fmt.RoundView) : Prop where
  items : r.vals.map itemOf = d.items.filter (· != .root)
  logN : d.entry.logN ≤ 64
  drawn : DrawnIs d.entry d.kind r.drawn

theorem gplain_old {W P : Type} : ∀ (b : ℕ) (p : P) (ν : W), GPlain.old (GPlain.mk b p ν) = p
  | 0, _, _ => rfl
  | _ + 1, _, _ => rfl

theorem gchal_old {C : Type} : ∀ (b : ℕ) (c : C), GChal.old (GChal.zero b c) = c
  | 0, _ => rfl
  | _ + 1, _ => rfl

theorem gchal_pass {C : Type} : ∀ (b : ℕ) (c : C), GChal.pass (GChal.zero b c) = true
  | 0, _ => decide_eq_true fun i => i.elim0
  | _ + 1, _ => decide_eq_true fun _ => rfl

/-- One written oracle a round. -/
def Orcs : List PQ.RD → Type
  | [] => Unit
  | d :: ds => (wRound d).Orc × Orcs ds

/-- The written oracles of a transcript. -/
def orcsOf : (ds : List PQ.RD) → Tr (PQ.uL (ckP .two) ds) → Orcs ds
  | [], _ => ()
  | _ :: ds, (m, _, τ) => (m.1, orcsOf ds τ)


theorem tr_onto : ∀ (ds : List PQ.RD) (rs : List Fmt.RoundView), List.Forall₂ RoundIs ds rs →
    ∀ os : Orcs ds, ∃ τ : Tr (PQ.uL (ckP .two) ds),
      (PQ.rvSL (ckP .two) ds τ).map noDigest = rs.map noDigest ∧
      PQ.passSL (ckP .two) ds (PQ.rhoSL (ckP .two) ds τ) = true ∧ orcsOf ds τ = os
  | [], [], _, _ => ⟨(), rfl, rfl, rfl⟩
  | d :: ds, r :: rs, h, (o, os) => by
    cases h with
    | cons hr hrs =>
      obtain ⟨τ, a, b, c⟩ := tr_onto ds rs hrs os
      obtain ⟨x, hx⟩ := plain_onto d.items r.vals hr.items
      obtain ⟨u, hu⟩ := drawn_of_blocks d.entry d.kind r.drawn hr.logN hr.drawn
      refine ⟨((o, GPlain.mk d.entry.work x (default : ℕ)), GChal.zero d.entry.work u, τ), ?_, ?_,
          ?_⟩
      · show noDigest ⟨PQ.PlainOf.gots d.items (GPlain.old (GPlain.mk d.entry.work x (default :
          ℕ))),
          (ckP .two).dr d.entry d.kind (GChal.old (GChal.zero d.entry.work u))⟩ ::
            (PQ.rvSL (ckP .two) ds τ).map noDigest = noDigest r :: rs.map noDigest
        rw [gplain_old, gchal_old, a, hx]
        congr 1
        show (⟨r.vals, { (ckP .two).dr d.entry d.kind u with digest := none }⟩ : Fmt.RoundView) =
          ⟨r.vals, { r.drawn with digest := none }⟩
        rw [hu]
      · show (GChal.pass (GChal.zero d.entry.work u) &&
          PQ.passSL (ckP .two) ds (PQ.rhoSL (ckP .two) ds τ)) = true
        rw [gchal_pass, b]
        rfl
      · show (o, orcsOf ds τ) = (o, os)
        rw [c]

/-- A transcript with any written oracles: no premise. -/
theorem tr_with : ∀ (ds : List PQ.RD) (os : Orcs ds),
    ∃ τ : Tr (PQ.uL (ckP .two) ds), orcsOf ds τ = os
  | [], _ => ⟨(), rfl⟩
  | d :: ds, (o, os) => by
    obtain ⟨τ, h⟩ := tr_with ds os
    exact ⟨((o, (wRound d).dPlain), Classical.choice (wRound d).neChal, τ), by
      show (o, orcsOf ds τ) = (o, os)
      rw [h]⟩

theorem roundsFit_noDigest : ∀ (ds : List Fmt.DeclaredRound) (rs : List Fmt.RoundView),
    roundsFit ds (rs.map noDigest) = roundsFit ds rs
  | [], [] => rfl
  | [], _ :: _ => rfl
  | _ :: _, [] => rfl
  | d :: ds, r :: rs => by
    show (_ && roundsFit ds (rs.map noDigest)) = (_ && roundsFit ds rs)
    rw [roundsFit_noDigest ds rs]
    rfl

theorem groupsOf_noDigest (F : ℕ) : ∀ (ds : List Fmt.DeclaredRound) (rs : List Fmt.RoundView),
    groupsOf F ds ((rs.map noDigest).map (·.drawn)) = groupsOf F ds (rs.map (·.drawn))
  | [], [] => rfl
  | [], _ :: _ => rfl
  | _ :: _, [] => rfl
  | d :: ds, r :: rs => by
    show _ ++ _ ++ groupsOf F ds ((rs.map noDigest).map (·.drawn)) =
      _ ++ _ ++ groupsOf F ds (rs.map (·.drawn))
    rw [groupsOf_noDigest F ds rs]
    rfl

theorem noDigest_idem (rs : List Fmt.RoundView) : (rs.map noDigest).map noDigest = rs.map noDigest := by
  rw [List.map_map]
  rfl

/-- Block.step reads its rounds without the sealed digest. -/
theorem step_noDigest {S Cl : Type} (F : ℕ) (b : Block S Cl) (s : S) (rs : List Fmt.RoundView)
    (cols : List OpenedColumn) : b.step F s (rs.map noDigest) cols = b.step F s rs cols := by
  unfold Block.step
  rw [roundsFit_noDigest, groupsOf_noDigest, noDigest_idem]

theorem step_congr {S Cl : Type} (F : ℕ) (b : Block S Cl) (s : S) (rs rs' : List Fmt.RoundView)
    (cols : List OpenedColumn) (h : rs.map noDigest = rs'.map noDigest) :
    b.step F s rs cols = b.step F s rs' cols := by
  rw [← step_noDigest F b s rs, ← step_noDigest F b s rs', h]

end H2K.Onto

#print axioms H2K.Onto.tr_onto
#print axioms H2K.Onto.tr_with
#print axioms H2K.Onto.step_congr
