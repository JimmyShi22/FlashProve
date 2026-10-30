-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Close/Law/KindK10.lean (kind K10): K10's SHARE OF THE CHAIN OF PROMISES, SECOND
FORM (`KindTiedR`, Johnson/Desc/Sound/TiedR.lean: the form in which the join takes a kind's law),
FROM ONE NAMED CONDITION. THE FOUR WORDS OF THE TIE ARE PICKED. Definitions, statements and proofs.
A file BESIDE the table of joints: it turns nothing of it.

Why. `TiedAtR` (Johnson/Desc/Sound/ChainOfPromisesR.lean) says: there are a condition in front o, a
condition behind o', a relation in front R and a relation behind R' with eight clauses: the piece's
law (`GoodIn o o' R R'`), five ties to the table, "a mark stays", "decodes rides". This file names
that form for this kind.
THE PICK. o' := true. R := the table's own relation on what the sub-protocol closes and reads
(`relAt` of `meansQ` at `insQ`). R' := the table's own relation on what it opens and reads (at
`outsQ`). o: a letter here; meant: K10's condition in front `K10OnS` (AtBlockSelf.lean), read at the
pair. With this pick THE THIRD AND THE FOURTH TIE HOLD BY "fun h => h": their weight lies in the
law's own premise hQ (`k10_goodIn`, GoodOf.lean): a witness of the table's relation behind, carried
through the table's extractor, is a witness of the table's relation in front.
  `tiedAtR_of_picks` (general in the kind): `TiedAtR` at that pick from: the law; the first, second
    and fifth tie; the mark; decodes.
  `held_step`: let b be a sub-protocol whose yes is a yes of `closeFrame`, read and written as K10
    reads and writes (H). Where the maker's piece of b (`pieceOf (held b) ..`), with any map as its
    extractor, puts out a' from a: the public part stays; `K10Step a.1.2 a'.1.2`; the strings behind
    are what the library's stage leaves (`Behind`, T2AtPiece.lean).
  `K10CondAt .. k q o Fn base`: THE CONDITION AT ONE PLACE, ONE FIELD A DEBT: law; front (the first
    tie); fence ("reached" gives Fn); asks (`K10AsksR Fn`, AsksOfMgR.lean: what the second tie asks
    of the meaning); dec (decodes rides, unfenced: the form's last clause has no "reached" in hand);
    kept, trees, msgs (three facts on the table's numbers); back (the fifth tie, in the form's own
    words); step (what `held_step` gives).
  `k10_tied_at`: `K10CondAt`, the two tests on the table, ps[k]? = some p of the kind K10: `TiedAtR
    .. k q`.
  `K10Cond .. E l`: at every place of the kind K10 there are o, Fn, base with `K10CondAt` at the
    piece with the table's extractor. `k10_kind`: THEN `KindTiedR .. E l .K10`.
Limits. A BUNDLING: `K10Cond` IS SHOWN OF NOTHING. Two of its fields name parts of the conclusion:
law (`GoodIn`) and back (the fifth tie, word for word). front is not typed anywhere else; whether
`K10OnS` can be met at a reached state is not shown. Nothing on soundness.

-/
import Johnson.Desc.First.Close.Law.AsksOfMgR
import Johnson.Desc.First.Close.Law.HandsOfK10
import Johnson.Desc.First.Close.Law.GoodAtMaker
import Johnson.Desc.Sound.TiedR
import Johnson.Desc.Sound.KeySeatsAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Close

open OnBytes OnBytes.Slice OnBytes.Flat OnBytes.Maker KObj
open _root_.Run (ckP)
open _root_.Run.PQ (CK)
open VerifiableInference.Desc (KindName Strs)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.K9 (recOf putRec)
open VerifiableInference.Desc.First (Numbers Item Pub Meaning ModelPart onAt openSets pubSets start
  closersFit closersNext k10_promise_at)

section
variable {Pz Wt Cl : Type} {C : CK} {F : Frame} (Nu : Numbers) (Mg : Meaning Pz Wt)
  (links : List ModelPart) (ps : List Place)
  (Rch : ℕ → (Pz × VerifiableInference.Desc.First.S) × F.E.Str → Prop)

/-- **The form at the pick**: o' := true; the two relations are the table's own. -/
theorem tiedAtR_of_picks (k : ℕ) (q : Piece C F (Pz × VerifiableInference.Desc.First.S) Cl Wt)
    (o : (Pz × VerifiableInference.Desc.First.S) × F.E.Str → Prop)
    (law : q.GoodIn o (fun _ => True) (relAt (meansQ Nu Mg fun a => a) (insQ links ps k))
      (relAt (meansQ Nu Mg fun a => a) (outsQ links ps k)))
    (t1 : ∀ a, onQ Nu Mg links ps (fun a => a) k a → Rch k a → ¬ a.1.2.failed ≠ none → o a)
    (t2 : ∀ a τ b, onQ Nu Mg links ps (fun a => a) k a → Rch k a → ¬ a.1.2.failed ≠ none →
      q.ior.red.out a τ = some b → onQ Nu Mg links ps (fun a => a) (k + 1) b)
    (t5 : ∀ a τ b w i, onQ Nu Mg links ps (fun a => a) k a → Rch k a → ¬ a.1.2.failed ≠ none →
      q.ior.red.out a τ = some b → onQ Nu Mg links ps (fun a => a) (k + 1) b →
      relQ Nu Mg links ps (fun a => a) (k + 1) b w →
      openAfter (insQ links ps) (outsQ links ps) (· ∈ start links) k i → ¬ insQ links ps k i →
      meansQ Nu Mg (fun a => a) i a (q.ext a τ w))
    (mark : ∀ a τ b, q.ior.red.out a τ = some b → a.1.2.failed ≠ none → b.1.2.failed ≠ none)
    (dec : ∀ a τ b, q.ior.red.out a τ = some b → Mg.decodes a.1 (strsOf F a.2) →
      Mg.decodes b.1 (strsOf F b.2)) :
    TiedAtR Nu Mg links ps (fun a => a) Rch k q :=
  ⟨o, fun _ => True, _, _, law, t1, fun a τ b h1 h2 h3 h4 _ => t2 a τ b h1 h2 h3 h4,
    fun _ _ _ _ _ _ _ _ _ h => h, fun _ _ _ _ _ _ _ _ _ _ h => h, t5, mark, dec⟩

end

section
variable {Pz Wt Cl : Type} {F : Frame}

/-- **What the maker's piece's out holds**, with any map as its extractor. -/
theorem held_step (Pr : Par) (b : Block VerifiableInference.Desc.First.S Cl)
    (H : ∀ s rs gs s', b.decide s rs gs = .ok s' → ∃ x, closeFrame (rdK s).1 (rdK s).2.1
      (rdK s).2.2 (entries Pr) rs = .ok x ∧ s' = wrK s x.1 x.2)
    (base : ℕ) (ds : List RDT)
    (x : Rest (ckP .two) F (Pz × VerifiableInference.Desc.First.S) Wt ds)
    (e : (Pz × VerifiableInference.Desc.First.S) × F.E.Str →
      (Pz × VerifiableInference.Desc.First.S) × F.E.Str → Wt → Wt)
    (a a' : (Pz × VerifiableInference.Desc.First.S) × F.E.Str)
    (τ : Iop.Tr (uLT (ckP .two) ((pieceOf (held b) base ds [] x).withMap e).ds))
    (h : ((pieceOf (held b) base ds [] x).withMap e).ior.red.out a τ = some a') :
    a'.1.1 = a.1.1 ∧ K10Step a.1.2 a'.1.2 ∧ Behind F base (strsOf F a.2) (strsOf F a'.2) := by
  obtain ⟨-, -, ⟨gs, hd⟩, hi⟩ := Piece.out_decide _ a a' τ h
  obtain ⟨s', hs', he⟩ := held_decide b a.1 a'.1 _ gs hd
  obtain ⟨y, hy, hw⟩ := H _ _ _ _ hs'
  refine ⟨by rw [he], ⟨_, _, y, hy, by rw [he]; exact hw⟩, ⟨ds, a.2, τ, rfl, by rw [hi]; rfl⟩⟩

end

section
variable {Pz Wt Cl : Type} {F : Frame} (Nu : Numbers) (Mg : Meaning Pz Wt)
  (links : List ModelPart) (ps : List Place)
  (Rch : ℕ → (Pz × VerifiableInference.Desc.First.S) × F.E.Str → Prop)

/-- **THE CONDITION AT ONE PLACE OF THE KIND K10, ONE FIELD A DEBT.** -/
structure K10CondAt (k : ℕ)
    (q : Piece (ckP .two) F (Pz × VerifiableInference.Desc.First.S) Cl Wt)
    (o : (Pz × VerifiableInference.Desc.First.S) × F.E.Str → Prop)
    (Fn : VerifiableInference.Desc.First.S → Prop) (base : ℕ) : Prop where
  /-- the piece's law, at the pick -/
  law : q.GoodIn o (fun _ => True) (relAt (meansQ Nu Mg fun a => a) (insQ links ps k))
    (relAt (meansQ Nu Mg fun a => a) (outsQ links ps k))
  /-- the first tie: the table's promise at a reached state without a mark gives the law's own
  condition in front -/
  front : ∀ a, onQ Nu Mg links ps (fun a => a) k a → Rch k a → ¬ a.1.2.failed ≠ none → o a
  /-- "reached" gives the fence -/
  fence : ∀ a, Rch k a → Fn a.1.2
  /-- what the second tie asks of the meaning, at the fenced states -/
  asks : K10AsksR Fn Nu Mg ((openSets links ps (start links))[k]?.getD [])
    ((openSets links ps (start links))[k + 1]?.getD []) ((pubSets Mg.more links ps)[k]?.getD [])
    ((pubSets Mg.more links ps)[k + 1]?.getD []) (Behind F base)
  /-- "decodes" rides along K10's step, at every state -/
  dec : ∀ z s s' y y', K10Step s s' → Behind F base y y' → Mg.decodes (z, s) y →
    Mg.decodes (z, s') y'
  /-- what is kept lies in its group -/
  kept : ∀ p, ps[k]? = some p → ∀ t ∈ Nu.keptOf (p.link.getD 0), t ∈ Nu.group (p.link.getD 0)
  /-- the sub-protocol sends no tree -/
  trees : Nu.treesAt ps[k + 1]? = Nu.treesAt ps[k]?
  /-- and no message -/
  msgs : Nu.msgsAt ps[k + 1]? = Nu.msgsAt ps[k]?
  /-- the fifth tie, in the form's own words -/
  back : ∀ a τ b w i, onQ Nu Mg links ps (fun a => a) k a → Rch k a → ¬ a.1.2.failed ≠ none →
    q.ior.red.out a τ = some b → onQ Nu Mg links ps (fun a => a) (k + 1) b →
    relQ Nu Mg links ps (fun a => a) (k + 1) b w →
    openAfter (insQ links ps) (outsQ links ps) (· ∈ start links) k i → ¬ insQ links ps k i →
    meansQ Nu Mg (fun a => a) i a (q.ext a τ w)
  /-- what the piece's out holds -/
  step : ∀ a τ b, q.ior.red.out a τ = some b →
    b.1.1 = a.1.1 ∧ K10Step a.1.2 b.1.2 ∧ Behind F base (strsOf F a.2) (strsOf F b.2)

/-- **THE FORM AT ONE PLACE, FROM THE CONDITION.** -/
theorem k10_tied_at (k : ℕ) (p : Place)
    (q : Piece (ckP .two) F (Pz × VerifiableInference.Desc.First.S) Cl Wt)
    (o : (Pz × VerifiableInference.Desc.First.S) × F.E.Str → Prop)
    (Fn : VerifiableInference.Desc.First.S → Prop) (base : ℕ)
    (hF : closersFit links ps (start links) = true) (hX : closersNext links ps = true)
    (hk : ps[k]? = some p) (hK : p.kind = .K10)
    (Cd : K10CondAt Nu Mg links ps Rch k q o Fn base) :
    TiedAtR Nu Mg links ps (fun a => a) Rch k q := by
  refine tiedAtR_of_picks Nu Mg links ps Rch k q o Cd.law Cd.front ?_ Cd.back ?_ ?_
  · intro a τ b ha hr _ hb
    obtain ⟨e1, hs, hB⟩ := Cd.step a τ b hb
    obtain ⟨es, rs, x, hx, hw⟩ := hs
    have hs' : K10Step a.1.2 b.1.2 := ⟨es, rs, x, hx, hw⟩
    have hf := Cd.fence a hr
    have e := k10_promise_at Nu Mg links ps k p hF hX hk hK (Cd.kept p hk) Cd.trees Cd.msgs
      ((pubSets Mg.more links ps)[k]?.getD []) ((pubSets Mg.more links ps)[k + 1]?.getD [])
      (a.1.1, a.1.2) a.1.1 (strsOf F a.2) (strsOf F b.2) es rs x hx ha
    rw [← hw, ← e1] at e
    exact e (Cd.asks.dec _ _ _ _ _ hf hs' hB) (Cd.asks.inOrder _ _ _ hf hs')
      (Cd.asks.pub _ _ _ hf hs') (Cd.asks.pubP _ _ _ hf hs') (Cd.asks.held _ _ _ hf hs')
      (Cd.asks.shown _ _ _ _ _ hf hs' hB)
  · intro a τ b hb hm
    rw [k10_step_mark (Cd.step a τ b hb).2.1]
    exact hm
  · intro a τ b hb hd
    obtain ⟨e1, hs, hB⟩ := Cd.step a τ b hb
    have := Cd.dec a.1.1 a.1.2 b.1.2 _ _ hs hB hd
    rw [← e1] at this
    exact this

variable (E : ℕ → (Pz × VerifiableInference.Desc.First.S) × F.E.Str →
    (Pz × VerifiableInference.Desc.First.S) × F.E.Str → Wt → Wt)
  (l : List (Piece (ckP .two) F (Pz × VerifiableInference.Desc.First.S) Cl Wt))

/-- **THE ONE CONDITION FOR THIS KIND OF STEP.** -/
def K10Cond : Prop :=
  ∀ i q a, l[i]? = some q → ps[i]? = some a → a.kind = KindName.K10 →
    ∃ (o : (Pz × VerifiableInference.Desc.First.S) × F.E.Str → Prop)
      (Fn : VerifiableInference.Desc.First.S → Prop) (base : ℕ),
      K10CondAt Nu Mg links ps Rch i (q.withMap (E i)) o Fn base

/-- **K10's SHARE OF THE CHAIN OF PROMISES, SECOND FORM, FROM THE ONE CONDITION.** -/
theorem k10_kind (hF : closersFit links ps (start links) = true)
    (hX : closersNext links ps = true) (Cd : K10Cond Nu Mg links ps Rch E l) :
    KindTiedR Nu Mg links ps Rch E l .K10 := by
  intro i q a hq ha hk
  obtain ⟨o, Fn, base, h⟩ := Cd i q a hq ha hk
  exact k10_tied_at Nu Mg links ps Rch i a _ o Fn base hF hX ha hk h

end

end VerifiableInference.Desc.First.Close

#print axioms VerifiableInference.Desc.First.Close.tiedAtR_of_picks
#print axioms VerifiableInference.Desc.First.Close.held_step
#print axioms VerifiableInference.Desc.First.Close.k10_tied_at
#print axioms VerifiableInference.Desc.First.Close.k10_kind
