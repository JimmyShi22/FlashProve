-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/RunOne/KeyKeepsAt23.lean. THE KEY FILE, CHAINS 2 | 3: THE FOUR LAWS AT THE MAKER's OWN PIECES: the part cut off KeyKeeps23.lean THAT UNFOLDS THE SEATED BLOCKS' TEXTS (a move of declarations): front₂_same · chainEnd_same · sources_same · sources_yes · end₃_yes · held_hands · front₂_keeps · end₂_keeps · sources₃_keeps · end₃_keeps.
OBJECT: front₂ X of the key file's description · the chains' ends · takenSources (KeyCut23.lean's names of descriptionFromSource's own blocks). USER: four fields of The35 (Johnson/Top/Fire/Code/The35.lean). LETTERS: general in F · G · at_ · R · coll …. IT HANGS ON THE TEXTS OF THE DESCRIPTION's BLOCKS.
Nothing on soundness.
-/
import Johnson.RunOne.KeyKeeps23
import Johnson.RunOne.KeyCut23


set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.RunOne.KeyRows23
open OnBytes OnBytes.Params
open VerifiableInference.Desc VerifiableInference.Desc.Key VerifiableInference.Desc.Sound VerifiableInference.Desc.Plain
open OnBytes.Maker OnBytes.Flat KObj
open _root_.Run.PQ (CK)
open _root_.Iop (Reduction)

/-! ## The four blocks hand the record on -/

theorem front₂_same (X : Source) (s : St₂) (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64))) (s' : St₂) (h : (front₂ X).decide s rs gs = .ok s') : s' = s :=
  (Except.ok.inj h).symm

theorem chainEnd_same {σ Cl : Type} (chain piece : Nat) (sealed : Bool) (inFront : List Fmt.DeclaredRound) (asks : σ → ChainEnd.Clauses)
    (s : σ) (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64))) (s' : σ) (h : (ChainEnd.chainEnd chain piece sealed inFront asks : Block σ Cl).decide s rs gs = .ok s') : s' = s := by
  have h' : ((ChainEnd.refuse (asks s)).map fun _ => s) = .ok s' := h
  cases hr : ChainEnd.refuse (asks s) with
  | error e => rw [hr] at h'; cases h'
  | ok u => rw [hr] at h'; exact (Except.ok.inj h').symm

theorem sources_same {Cl : Type} (own : Block St₃ Cl) (s : St₃) (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64))) (s' : St₃)
    (h : (VerifiableInference.Desc.Third.takenSources own : Block St₃ Cl).decide s rs gs = .ok s') : s' = s := by
  have h' : (do
      let ts ← named "every member of the own group, and the mask, has a tree in the book" (VerifiableInference.Desc.Third.takenOf s)
      need "every such tree is declared as taken from the chain that sent it" (ts.all fun x => VerifiableInference.Desc.Third.opensTaken own.rounds x.1 x.2)
      need "no other tree is declared as taken"
        ((own.rounds.flatMap (·.opens)).all fun o =>
          match o.2 with
          | .own _ => true
          | .taken c n => ts.contains (c, n))
      pure s : Except String St₃) = .ok s' := h
  obtain ⟨ts, -, h1⟩ := bindOk h'
  obtain ⟨_, -, h2⟩ := bindOk h1
  obtain ⟨_, -, h3⟩ := bindOk h2
  exact (Except.ok.inj h3).symm

/-- The yes of «the taken trees' sources» is its test, as the table's Bool has it. -/
theorem sources_yes (own : Block St₃ Unit) (s : St₃) (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64))) (s' : St₃)
    (h : (VerifiableInference.Desc.Third.takenSources own : Block St₃ Unit).decide s rs gs = .ok s') : srcOk own s = true := by
  have h' : (do
      let ts ← named "every member of the own group, and the mask, has a tree in the book" (VerifiableInference.Desc.Third.takenOf s)
      need "every such tree is declared as taken from the chain that sent it" (ts.all fun x => VerifiableInference.Desc.Third.opensTaken own.rounds x.1 x.2)
      need "no other tree is declared as taken"
        ((own.rounds.flatMap (·.opens)).all fun o =>
          match o.2 with
          | .own _ => true
          | .taken c n => ts.contains (c, n))
      pure s : Except String St₃) = .ok s' := h
  obtain ⟨ts, h0, h1⟩ := bindOk h'
  obtain ⟨_, h2, h3⟩ := bindOk h1
  obtain ⟨_, h4, -⟩ := bindOk h3
  have e0 : VerifiableInference.Desc.Third.takenOf s = some ts := by
    cases ht : VerifiableInference.Desc.Third.takenOf s with
    | none => rw [ht] at h0; cases h0
    | some t => rw [ht] at h0; exact congrArg some (Except.ok.inj h0)
  have needT : ∀ (m : String) (c : Bool) (u : Unit), need m c = .ok u → c = true := by
    intro m c u hn
    cases c with
    | true => rfl
    | false => cases hn
  unfold srcOk
  rw [e0]
  exact Bool.and_eq_true _ _ ▸ ⟨needT _ _ _ h2, needT _ _ _ h4⟩

/-- **The yes of the last chain's end is the last chain's share of the description's last test.** -/
theorem end₃_yes (inFront : List (Block St₃ Unit)) (s : St₃) (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64))) (s' : St₃)
    (h : (VerifiableInference.Desc.Third.end₃ inFront : Block St₃ Unit).decide s rs gs = .ok s') : VerifiableInference.Desc.Third.fin₃ s = true := by
  have h' : ((ChainEnd.refuse (ChainEnd.untestedL s.st)).map fun _ => s) = .ok s' := h
  have hr : ChainEnd.refuse (ChainEnd.untestedL s.st) = .ok () := by
    cases hx : ChainEnd.refuse (ChainEnd.untestedL s.st) with
    | error e => rw [hx] at h'; cases h'
    | ok u => rfl
  cases h1 : s.st.groups.all (·.inRun) with
  | false => simp [ChainEnd.refuse, ChainEnd.untestedL, h1] at hr
  | true =>
    cases h2 : (s.st.oracles.all fun x => !x.sampled || x.groups.any fun g => (s.st.groups[g]?).any (·.inRun)) with
    | false => simp [ChainEnd.refuse, ChainEnd.untestedL, h1, h2] at hr
    | true =>
      unfold VerifiableInference.Desc.Third.fin₃
      rw [h1, Bool.true_and]
      rw [Array.all_eq_true_iff_forall_mem] at h2 ⊢
      intro x hx
      have h3 := h2 x hx
      cases hs : x.sampled with
      | false => rfl
      | true =>
        rw [hs] at h3
        cases hg : x.groups with
        | nil => rw [hg] at h3; simp at h3
        | cons g l => rfl

/-- The maker's held block hands the pair on wherever the description's block hands its record on. -/
theorem held_hands {P σ Cl : Type} (b : Block σ Cl) (h : ∀ s rs gs s', b.decide s rs gs = .ok s' → s' = s)
    (z : P × σ) (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64))) (z' : P × σ) (hd : (held b : Block (P × σ) Cl).decide z rs gs = .ok z') : z' = z := by
  obtain ⟨e1, e2⟩ := held_decide b z rs gs z' hd
  exact Prod.ext e1 (h _ _ _ _ e2)

/-! ## The four laws, at the maker's own pieces -/

section
variable {XI Cells M Smp Rec W : Type} {C : CK} (F : FileDescription XI) (Fr₂ Fr₃ : Frame)
  (G₂ : Reading (P₂ × St₂) Cells M Smp Rec) (G₃ : Reading (P₃ × St₃) Cells M Smp Rec) (at_ : Where)
  (S : LinShape) (K₁ : KPlan) (R : KRead Cells M) (enc : (Nat → E) → Nat → E) (rad a : Nat) (idx : List Nat)
  (coll : Strs → Rec → Prop) (last₁ : FirstState → Bool) (src : St₃ → Bool) (off₂ off₃ : Nat → Nat) (t₁ : Nat)
  (X : Source) (P : LaterPlaces)

/-- **2.0: the shared chain's front.** -/
theorem front₂_keeps (base : Nat) (ds : List RDT) (back : List Fmt.RoundView) (x : Rest C Fr₂ (P₂ × St₂) W ds)
    (hbase : ∀ k ∈ pinned seam, (at_ k).1 < base) (hc : CellOnly coll) :
    (pieceOf (held (front₂ X)) base ds back x).ior.red.Keeps (on₂ F Fr₂ G₂ at_ S K₁ R enc rad a coll last₁ off₂ 0) (on₂ F Fr₂ G₂ at_ S K₁ R enc rad a coll last₁ off₂ 1)
      (L₂ F Fr₂ G₂ at_ S K₁ R enc rad 0) (L₂ F Fr₂ G₂ at_ S K₁ R enc rad 1) (pieceOf (held (front₂ X)) base ds back x).err :=
  keeps₂_01 F Fr₂ G₂ at_ S K₁ R enc rad a coll last₁ off₂ (pieceOf (held (front₂ X)) base ds back x) (held_hands (front₂ X) (front₂_same X)) hbase hc

/-- **2.11: the end of chain 2.** -/
theorem end₂_keeps (base : Nat) (ds : List RDT) (back : List Fmt.RoundView) (x : Rest C Fr₂ (P₂ × St₂) W ds)
    (hbase : ∀ k ∈ pinned end₂, (at_ k).1 < base) (hc : CellOnly coll) :
    (pieceOf (held (seat (VerifiableInference.Desc.K12.Seat.last (inFront₂ X P)) : Block St₂ Claim)) base ds back x).ior.red.Keeps
      (on₂ F Fr₂ G₂ at_ S K₁ R enc rad a coll last₁ off₂ 11) (on₂ F Fr₂ G₂ at_ S K₁ R enc rad a coll last₁ off₂ 12)
      (L₂ F Fr₂ G₂ at_ S K₁ R enc rad 11) (L₂ F Fr₂ G₂ at_ S K₁ R enc rad 12)
      (pieceOf (held (seat (VerifiableInference.Desc.K12.Seat.last (inFront₂ X P)) : Block St₂ Claim)) base ds back x).err :=
  keeps₂_1112 F Fr₂ G₂ at_ S K₁ R enc rad a coll last₁ off₂ _
    (held_hands _ fun s rs gs s' h => chainEnd_same (Cl := Unit) 2 11 true ((inFront₂ X P).flatMap (·.rounds)) (fun d : St₂ => ChainEnd.untestedL d.st) s rs gs s' h) hbase hc

/-- **3.1: the taken trees' sources.** -/
theorem sources₃_keeps (base : Nat) (ds : List RDT) (back : List Fmt.RoundView) (x : Rest C Fr₃ (P₃ × St₃) W ds)
    (hbase : ∀ k ∈ pinned (open₃ 1), (at_ k).1 < base) (hc : CellOnly coll) :
    (pieceOf (held (seat (VerifiableInference.Desc.Third.takenSources (ownTest P)) : Block St₃ Claim)) base ds back x).ior.red.Keeps
      (on₃ F Fr₃ G₃ at_ S K₁ R a idx coll (srcOk (ownTest P)) off₂ off₃ t₁ 1) (on₃ F Fr₃ G₃ at_ S K₁ R a idx coll (srcOk (ownTest P)) off₂ off₃ t₁ 2) (L₃ F Fr₃ G₃ at_ S K₁ R 1) (L₃ F Fr₃ G₃ at_ S K₁ R 2)
      (pieceOf (held (seat (VerifiableInference.Desc.Third.takenSources (ownTest P)) : Block St₃ Claim)) base ds back x).err :=
  keeps₃_12 F Fr₃ G₃ at_ S K₁ R a idx coll (srcOk (ownTest P)) off₂ off₃ t₁ _ (held_hands _ fun s rs gs s' h => sources_same (ownTest P) s rs gs s' h)
    (fun z rs gs hd => sources_yes (ownTest P) z.2 rs gs z.2 (held_decide _ z rs gs z hd).2) hbase hc

/-- **3.3: the end of chain 3**: at whatever rounds stand in front. -/
theorem end₃_keeps (inFront : List (Block St₃ Unit)) (base : Nat) (ds : List RDT) (back : List Fmt.RoundView) (x : Rest C Fr₃ (P₃ × St₃) W ds) (hc : CellOnly coll) :
    (pieceOf (held (seat (VerifiableInference.Desc.Third.end₃ inFront) : Block St₃ Claim)) base ds back x).ior.red.Keeps
      (on₃ F Fr₃ G₃ at_ S K₁ R a idx coll src off₂ off₃ t₁ 3) (on₃ F Fr₃ G₃ at_ S K₁ R a idx coll src off₂ off₃ t₁ 4) (L₃ F Fr₃ G₃ at_ S K₁ R 3) (L₃ F Fr₃ G₃ at_ S K₁ R 4)
      (pieceOf (held (seat (VerifiableInference.Desc.Third.end₃ inFront) : Block St₃ Claim)) base ds back x).err :=
  keeps₃_34 F Fr₃ G₃ at_ S K₁ R a idx coll src off₂ off₃ t₁ _ (held_hands _ fun s rs gs s' h => chainEnd_same (Cl := Unit) 3 3 false (inFront.flatMap (·.rounds)) (fun d : St₃ => ChainEnd.untestedL d.st) s rs gs s' h)
    (fun z rs gs hd => end₃_yes inFront z.2 rs gs z.2 (held_decide _ z rs gs z hd).2) hc

end


end Johnson.RunOne.KeyRows23

#print axioms Johnson.RunOne.KeyRows23.end₃_yes
#print axioms Johnson.RunOne.KeyRows23.sources_yes
#print axioms Johnson.RunOne.KeyRows23.front₂_keeps
#print axioms Johnson.RunOne.KeyRows23.end₂_keeps
#print axioms Johnson.RunOne.KeyRows23.sources₃_keeps
#print axioms Johnson.RunOne.KeyRows23.end₃_keeps
#print axioms Johnson.RunOne.KeyRows23.front₂_same
#print axioms Johnson.RunOne.KeyRows23.chainEnd_same
#print axioms Johnson.RunOne.KeyRows23.sources_same
