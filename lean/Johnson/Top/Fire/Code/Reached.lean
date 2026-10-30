-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Top/Fire/Code/Reached.lean: A HISTORY IN A GENERIC FORM, OVER THE MAKER's OWN PIECES: «this state was reached: from a start, the chain's first k blocks have each said yes, at some rounds and columns, and have led here». Book-keeping, general in the description.

Why. One kind's laws are proved under promises that are HISTORIES in its own text's functions; the tables' promises are ties on a state. A state may satisfy every tie and be reached by no run. Here the history is said once, with no letter of any kind: of a list of blocks alone.
Main names.
  `Reached ft bs st₀ k a`: k = 0: `st₀ a` (the chain's start, a letter) · k + 1: there are a state a', rounds rs and columns cols with `Reached ft bs st₀ k a'`, and THE k-TH BLOCK's STEP (`Block.step`: the two tests in front of the decision, and the decision) says yes at a' rs cols and leads to a. THE STATE ALONE: no oracle's strings, no transcript. ft: the number of the chain's first tree.
  `piece_steps_at`: where a piece's reduction puts out b, its block's step said yes on the transcript's own rounds and the stage's own opened columns (what `piece_decides_at` and `piece_fits_at` each read a half of).
  `Reached.last`: so of one step BOTH come out: the block's decision went on (`step_decides`) and the rounds fit the declared ones (`step_fits`).
  `reached_step`: EVERY PIECE EARNS THE NEXT ONE FOR NOTHING: where a piece whose block is the k-th puts out b from a, `Reached … k a.1` gives `Reached … (k + 1) b.1` (`piece_steps_at`).
  `keeps_reached`: so a law MAY SPEND THE HISTORY IN FRONT AND NEED NOT EARN IT BEHIND: `Keeps (on ∧ Reached k) on' L L'` gives `Keeps (on ∧ Reached k) (on' ∧ Reached (k + 1)) L L'`, at the same errors.
  `KeepsAt.reached`: a law that does not know the history rides: `KeepsAt on L ps n` gives `KeepsAt (on ∧ Reached) L ps n`.
  `rowBlocks₁` | `₂` | `₃`: at the maker's own rows the n-th piece's block is the n-th of `(cⱼ :: kⱼ).map held`.
SO NO TABLE's BINDER NEED TURN: the history is woven in at the frame: the tables `fun k x => on k x ∧ Reached ft bs st₀ k x.1`.
THE SILLY MEMBERS. st₀ := «never»: nothing is reached, and every law under the history holds for nothing: a start is worth what the seam gives: at border 0 the seam must hand `st₀` · bs := []: nothing behind border 0 is reached · st₀ := «always»: a history from ANY state: that is what the histories spoken of under Why are («there is a d0»).
THE MEMBER: an honest walk's states are reached by construction.
Limits. It says nothing of the oracles' strings, nor that the rounds were the transcript's (`piece_steps_at` knows that; it is forgotten here). Nothing on soundness.

-/
import Johnson.Top.Fire.Code.RowPieces
import Johnson.Desc.Plain.PieceFits

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace LPFD
open OnBytes.Maker OnBytes.Flat KObj
open _root_.Run.PQ (CK)
open VerifiableInference.Desc VerifiableInference.Desc.Sound VerifiableInference.Desc.Plain

section
variable {S Cl : Type}

/-- **This state was reached.** -/
def Reached (ft : ℕ) (bs : List (Block S Cl)) (st₀ : S → Prop) : ℕ → S → Prop
  | 0, a => st₀ a
  | k + 1, a => ∃ (a' : S) (b : Block S Cl) (rs : List _root_.Fmt.RoundView) (cols : List OpenedColumn) (n : ℕ),
      Reached ft bs st₀ k a' ∧ bs[k]? = some b ∧ b.step ft a' rs cols = .ok (a, n)

/-- **Of one step both come out**: the decision went on, and the rounds fit the declared ones. -/
theorem Reached.last {ft : ℕ} {bs : List (Block S Cl)} {st₀ : S → Prop} {k : ℕ} {a : S} (h : Reached ft bs st₀ (k + 1) a) :
    ∃ (a' : S) (b : Block S Cl) (rs : List _root_.Fmt.RoundView) (cols : List OpenedColumn), Reached ft bs st₀ k a' ∧ bs[k]? = some b ∧
      b.decide a' (rs.map noDigest) (groupsAt ft b rs cols) = .ok a ∧ roundsFit b.rounds rs = true := by
  obtain ⟨a', b, rs, cols, n, hr, hb, hs⟩ := h
  exact ⟨a', b, rs, cols, hr, hb, step_decides hs, (step_fits hs).1⟩

variable {C : CK} {Fr : Frame} {W : Type}

/-- **Where a piece's reduction puts out b: its block's step said yes**, on the transcript's own rounds and the stage's own opened columns. -/
theorem piece_steps_at (p : Piece C Fr S Cl W) (a : S × Fr.E.Str) (τ : Iop.Tr (uLT C p.ds)) (b : S × Fr.E.Str)
    (hb : p.ior.red.out a τ = some b) :
    ∃ n, p.b.step Fr.ft a.1 (rvT C p.ds τ ++ p.back) (sView C p.stage a.2 τ).opened = .ok (b.1, n) := by
  obtain ⟨s', k, hst, H'⟩ := foldConsOk (chainAtOk (pieceOk p a τ b hb))
  have e : (s', (rvT C p.ds τ ++ p.back).drop p.b.rounds.length, _) =
      (b.1, ([] : List _root_.Fmt.RoundView), ([] : List OpenedColumn)) := Except.ok.inj H'
  have e₁ : s' = b.1 := congrArg Prod.fst e
  have e₂ : (rvT C p.ds τ ++ p.back).drop p.b.rounds.length = [] := congrArg (fun x => x.2.1) e
  have e₃ : (rvT C p.ds τ ++ p.back).take p.b.rounds.length = rvT C p.ds τ ++ p.back :=
    List.take_of_length_le (List.drop_eq_nil_iff.1 e₂)
  rw [e₃, e₁] at hst
  exact ⟨k, hst⟩

/-- **Every piece earns the next history for nothing.** -/
theorem reached_step (bs : List (Block S Cl)) (st₀ : S → Prop) (k : ℕ) (p : Piece C Fr S Cl W) (hb : bs[k]? = some p.b)
    (a : S × Fr.E.Str) (τ : Iop.Tr (uLT C p.ds)) (b : S × Fr.E.Str) (h : p.ior.red.out a τ = some b) (hr : Reached Fr.ft bs st₀ k a.1) :
    Reached Fr.ft bs st₀ (k + 1) b.1 := by
  obtain ⟨n, hs⟩ := piece_steps_at p a τ b h
  exact ⟨a.1, p.b, _, _, n, hr, hb, hs⟩

/-- **A law may spend the history in front and need not earn it behind.** -/
theorem keeps_reached (bs : List (Block S Cl)) (st₀ : S → Prop) (k : ℕ) (p : Piece C Fr S Cl W) (hb : bs[k]? = some p.b)
    (on on' L L' : S × Fr.E.Str → Prop)
    (h : p.ior.red.Keeps (fun x => on x ∧ Reached Fr.ft bs st₀ k x.1) on' L L' p.err) :
    p.ior.red.Keeps (fun x => on x ∧ Reached Fr.ft bs st₀ k x.1) (fun x => on' x ∧ Reached Fr.ft bs st₀ (k + 1) x.1) L L' p.err :=
  Iop.Reduction.Leads.conseq h (fun _ ha => ha) fun a τ b ha hout hq => ⟨⟨hq.1, reached_step bs st₀ k p hb a τ b hout ha.2⟩, hq.2⟩

/-- **A law that does not know the history rides.** -/
theorem KeepsAt.reached (bs : List (Block S Cl)) (st₀ : S → Prop) {on L : ℕ → S × Fr.E.Str → Prop} {ps : List (Piece C Fr S Cl W)} {n : ℕ}
    (hbs : ∀ p, ps[n]? = some p → bs[n]? = some p.b) (h : KeepsAt on L ps n) :
    KeepsAt (fun k x => on k x ∧ Reached Fr.ft bs st₀ k x.1) L ps n := fun p hp =>
  keeps_reached bs st₀ n p (hbs p hp) (on n) (on (n + 1)) (L n) (L (n + 1))
    (Iop.Reduction.Leads.conseq (h p hp) (fun _ ha => ha.1) fun _ _ _ _ _ hq => hq)

end

section
variable {Xi W : Type} (C : CK) (F : FileDescription Xi) (D : WholeD)
    (c₁ : Block F.S₁ F.Cl) (k₁ : List (Block F.S₁ F.Cl)) (c₂ : Block F.S₂ F.Cl)
    (k₂ : List (Block F.S₂ F.Cl)) (c₃ : Block F.S₃ F.Cl) (k₃ : List (Block F.S₃ F.Cl))
    (rest₁ : (i : ℕ) → (ds : List RDT) → Rest C (frameAt D (allOf D) D.key₁ 0) (F.XiPub × F.S₁) W ds)
    (rest₂ : (i : ℕ) → (ds : List RDT) → Rest C (frameAt D (allOf D) D.key₂ 0) ((F.XiPub × F.S₁) × F.S₂) W ds)
    (rest₃ : (i : ℕ) → (ds : List RDT) → Rest C (frameAt D (allOf D) D.key₃ F.lastChainFirstTreeNumber) ((F.XiPub × F.S₁ × F.S₂) × F.S₃) W ds)
    (dW wEnd : W)

/-- At the maker's own row of chain 1 the n-th piece's block is the n-th block, held. -/
theorem rowBlocks₁ (n : ℕ) (p) (h : ((atDesc F (piecesAt C F D c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).p₁ :: (atDesc F (piecesAt C F D c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).l₁)[n]? = some p) :
    ((c₁ :: k₁).map held)[n]? = some p.b := by
  obtain ⟨b, base, ds, back, hb, rfl⟩ := rowGet₁ C F D c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd n p h
  rw [List.getElem?_map, hb]
  rfl

/-- At the maker's own row of chain 2 the n-th piece's block is the n-th block, held. -/
theorem rowBlocks₂ (n : ℕ) (p) (h : ((atDesc F (piecesAt C F D c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).p₂ :: (atDesc F (piecesAt C F D c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).l₂)[n]? = some p) :
    ((c₂ :: k₂).map held)[n]? = some p.b := by
  obtain ⟨b, base, ds, back, hb, rfl⟩ := rowGet₂ C F D c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd n p h
  rw [List.getElem?_map, hb]
  rfl

/-- At the maker's own row of chain 3 the n-th piece's block is the n-th block, held. -/
theorem rowBlocks₃ (n : ℕ) (p) (h : ((atDesc F (piecesAt C F D c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).p₃ :: (atDesc F (piecesAt C F D c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).l₃)[n]? = some p) :
    ((c₃ :: k₃).map held)[n]? = some p.b := by
  obtain ⟨b, base, ds, back, hb, rfl⟩ := rowGet₃ C F D c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd n p h
  rw [List.getElem?_map, hb]
  rfl

end

end LPFD

#print axioms LPFD.Reached.last
#print axioms LPFD.piece_steps_at
#print axioms LPFD.reached_step
#print axioms LPFD.keeps_reached
#print axioms LPFD.KeepsAt.reached
#print axioms LPFD.rowBlocks₁
#print axioms LPFD.rowBlocks₂
#print axioms LPFD.rowBlocks₃
