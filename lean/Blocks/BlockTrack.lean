-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Blocks/BlockTrack.lean: where the entries of a block's implicit output come from. (Block, implicit
part: Blocks/Block.lean. Words of this library: lean/GLOSSARY.md.)

`Block.Tracks` is closed under composition.

The implicit parts of statements are arbitrary types. What a relation uses of them is given by a
function rd : Y → N → E: the exposed entries. A block tracks if every entry that its output exposes
was exposed by its input or is entry (i, j) of a vector v sent in the block; src says which. Entries
of vectors are indexed by natural numbers, 0 outside the range, so that no statement needs a cast.

Notation: `nat v` (Blocks/Basic.lean): a vector as a function on ℕ, 0 beyond its end; from
Blocks/BlockFront.lean: `REnc F E r`: how the oracle part of one round of a block is sent;
`EncData F E s`: encoding data for all rounds of a list; `VIdx s d`: the vectors of all rounds;
`vecsN s d τ v i j`: entry (i, j) of the vector v of an unencoded transcript, 0 outside the range;
`vL`, `vR`: a vector of s, of t, as a vector of s ++ t.
-/
import Blocks.BlockFront

set_option linter.unusedSectionVars false

namespace Blocks
open Iop

section Tracks
variable {F E : Type} [Field F] [Field E] [Algebra F E]
  {Xi Yi Xo Yo X₁ Y₁ X₂ Y₂ X₃ Y₃ Ni No N₁ N₂ N₃ : Type}

/-- Where an exposed entry comes from: from the input, or from the vector v at (i, j). -/
abbrev Src (Ni : Type) (s : Shape) (d : EncData F E s) : Type := Ni ⊕ (VIdx s d × ℕ × ℕ)

/-- The block tracks: exposed entry n of its output has the value of `src n`. -/
def Block.Tracks (B : Block Xi Yi Xo Yo) (d : EncData F E B.shape) (rdi : Yi → Ni → E)
    (rdo : Yo → No → E) (src : No → Src Ni B.shape d) : Prop :=
  ∀ y τ n, rdo (B.imp y τ) n = Sum.elim (rdi y) (fun q => vecsN _ d τ q.1 q.2.1 q.2.2) (src n)

/-- the sources of two blocks in a row -/
def srcSeq {s t : Shape} (d₁ : EncData F E s) (d₂ : EncData F E t)
    (src₁ : N₂ → Src N₁ s d₁) (src₂ : N₃ → Src N₂ t d₂) :
    N₃ → Src N₁ (s ++ t) (d₁.app d₂) := fun n =>
  Sum.elim (fun m => Sum.elim Sum.inl (fun q => Sum.inr (vL d₁ d₂ q.1, q.2)) (src₁ m))
    (fun q => Sum.inr (vR d₁ d₂ q.1, q.2)) (src₂ n)

/-- Sequential composition. -/
theorem Block.Tracks.comp {B₁ : Block X₁ Y₁ X₂ Y₂} {B₂ : Block X₂ Y₂ X₃ Y₃}
    {d₁ : EncData F E B₁.shape} {d₂ : EncData F E B₂.shape} {r₁ : Y₁ → N₁ → E} {r₂ : Y₂ → N₂ → E}
    {r₃ : Y₃ → N₃ → E} {src₁ : N₂ → Src N₁ B₁.shape d₁} {src₂ : N₃ → Src N₂ B₂.shape d₂}
    (h₁ : B₁.Tracks d₁ r₁ r₂ src₁) (h₂ : B₂.Tracks d₂ r₂ r₃ src₂) :
    (B₁.seq B₂).Tracks (d₁.app d₂) r₁ r₃ (srcSeq d₁ d₂ src₁ src₂) := by
  intro y τ n
  show r₃ (B₂.imp (B₁.imp y (Tr.fst τ)) (Tr.snd (s := B₁.shape) τ)) n = _
  rw [h₂]
  unfold srcSeq
  rcases src₂ n with m | q
  · simp only [Sum.elim_inl]
    rw [h₁]
    rcases src₁ m with k | q
    · simp only [Sum.elim_inl]
    · simp only [Sum.elim_inr]
      exact (congrFun (congrFun (vecsN_vL d₁ d₂ τ q.1) _) _).symm
  · simp only [Sum.elim_inr]
    exact (congrFun (congrFun (vecsN_vR d₁ d₂ τ q.1) _) _).symm

/-- A block without rounds tracks if every entry of its output is an entry of its input. -/
theorem Block.tracks_pure {f : Xi → Option Xo} {g : Yi → Yo} {rdi : Yi → Ni → E} {rdo : Yo → No → E}
    (σ : No → Ni) (h : ∀ y n, rdo (g y) n = rdi y (σ n)) :
    (Block.pure f g).Tracks (F := F) PUnit.unit rdi rdo fun n => .inl (σ n) :=
  fun y _ n => h y n

/-- A block of one round tracks if (h) every entry of its output is an entry of the input or entry
(i, j) of the vector a of the message. -/
theorem Block.tracks_one {r : Round} {pb : Xi → r.Chal → r.Plain → Option Xo}
    {im : Yi → r.Msg → r.Chal → Yo} (e : REnc F E r) {rdi : Yi → Ni → E}
    {rdo : Yo → No → E} (src : No → Ni ⊕ (e.A × ℕ × ℕ))
    (h : ∀ y m c n, rdo (im y m c) n =
      Sum.elim (rdi y) (fun q => nat (fun i' => nat (e.vecE m.1 q.1 i') q.2.2) q.2.1) (src n)) :
    (Block.one r pb im).Tracks (e, PUnit.unit) rdi rdo fun n =>
      (src n).map id fun q => (.inl q.1, q.2) := by
  intro y τ n
  have h' := h y τ.1 τ.2.1 n
  show rdo (im y τ.1 τ.2.1) n = _
  rw [h']
  dsimp only
  rcases src n with k | q <;> rfl

/-- A block that acts on a part of a larger statement: an entry of the larger output is an entry of
the larger input or an entry of the part's output; an entry of the part's input is an entry of the
larger input. (not all hypotheses are named here: see the statement below) -/
theorem Block.Tracks.on {X Y X' Y' Mi Mo : Type} {B : Block Xi Yi Xo Yo} {d : EncData F E B.shape}
    {rdi : Yi → Ni → E} {rdo : Yo → No → E} {src : No → Src Ni B.shape d}
    (h : B.Tracks d rdi rdo src) (gx : X → Xi) (px : X → Xo → X') {gy : Y → Yi} {py : Y → Yo → Y'}
    {Rdi : Y → Mi → E} {Rdo : Y' → Mo → E} (κ : Ni → Mi) (σ : Mo → Mi ⊕ No)
    (hi : ∀ y k, rdi (gy y) k = Rdi y (κ k))
    (ho : ∀ y yo n, Rdo (py y yo) n = Sum.elim (Rdi y) (rdo yo) (σ n)) :
    (B.on gx px gy py).Tracks d Rdi Rdo fun n =>
      Sum.elim Sum.inl (fun m => (src m).map κ id) (σ n) := by
  intro y τ n
  show Rdo (py y (B.imp (gy y) τ)) n =
    Sum.elim (Rdi y) _ (Sum.elim Sum.inl (fun m => (src m).map κ id) (σ n))
  rw [ho]
  rcases σ n with k | m
  · rfl
  · simp only [Sum.elim_inr]
    rw [h]
    rcases src m with k | q
    · exact hi y k
    · rfl

end Tracks

/-! ## A sum with one term -/

section Claims
variable {F : Type} [Field F] {E : Type} [Field E] [Algebra F E]

private theorem sum_fin_ite {n : ℕ} (a : ℕ) (g : Fin n → E) :
    ∑ i : Fin n, (if a = i.val then g i else 0) = nat g a := by
  unfold nat
  by_cases h : a < n
  · rw [dif_pos h, Finset.sum_eq_single (⟨a, h⟩ : Fin n)]
    · exact if_pos rfl
    · intro b _ hb
      exact if_neg fun hab => hb (Fin.ext hab.symm)
    · intro hn
      exact absurd (Finset.mem_univ _) hn
  · rw [dif_neg h]
    exact Finset.sum_eq_zero fun i _ => if_neg fun (hai : a = i.val) => h (by rw [hai]; exact i.2)

end Claims

/-! ## Blocks/BlockLib.lean's blocks track -/

section Lib
variable {F E : Type} [Field F] [Field E] [Algebra F E] {Xi Yi Ni : Type}

/-- `sample` exposes what its input exposed. -/
theorem Block.tracks_sample {C : Type} [Fintype C] [Nonempty C]
    (ok : C → Bool) (rdi : Yi → Ni → E) :
    (Block.sample Xi Yi E C ok).Tracks (REnc.none E F Empty C, PUnit.unit) rdi rdi
      fun n => (Sum.inl n : Ni ⊕ (Empty × ℕ × ℕ)).map id fun q => (.inl q.1, q.2) :=
  Block.tracks_one (REnc.none E F Empty C) (fun n => Sum.inl n) fun _ _ _ _ => rfl

/-- `name` exposes what its input exposed and the entries of the vectors sent. -/
theorem Block.tracks_name {r : Round} (e : REnc F E r) (rdi : Yi → Ni → E) :
    (Block.name Xi Yi r).Tracks (e, PUnit.unit) rdi
      (fun yo =>
        Sum.elim (rdi yo.1) fun q : e.A × ℕ × ℕ =>
          nat (fun i' => nat (e.vecE yo.2 q.1 i') q.2.2) q.2.1)
      fun n => (n : Ni ⊕ (e.A × ℕ × ℕ)).map id fun q => (.inl q.1, q.2) :=
  Block.tracks_one e (fun n => n) fun _ _ _ n => by cases n <;> rfl

/-- `pads` exposes what its input exposed and the entries of the pad vector. -/
theorem Block.tracks_pads (C : Code.Enc F) [Nonempty (Fin C.n)] (q : ℕ) (rdi : Yi → Ni → E) :
    (Block.pads Xi Yi E C.msg).Tracks
      (REnc.ofV E Unit (fun _ => C) (fun _ => 1) (fun _ => 0) (fun _ => Role.pad)
          (fun _ => q) Empty Unit,
        PUnit.unit)
      rdi (fun yo => Sum.elim (rdi yo.1) yo.2) fun n =>
        ((n.map id fun j => ((), 0, j.val) : Ni ⊕ (Unit × ℕ × ℕ))).map id fun q =>
            (.inl q.1, q.2) :=
  Block.tracks_one (REnc.ofV
    E Unit (fun _ => C) (fun _ => 1) (fun _ => 0) (fun _ => Role.pad) (fun _ => q) Empty Unit)
    (fun n : Ni ⊕ Fin C.msg => n.map id fun j => ((), 0, j.val)) fun _ m _ n => by
      cases n with
      | inl k => rfl
      | inr j =>
        show m.1 () 0 j = nat (fun i' : Fin 1 => nat (m.1 () i') j.val) 0
        unfold nat
        rw [dif_pos Nat.one_pos]
        show m.1 () 0 j = if h : j.val < C.msg then m.1 () 0 ⟨j.val, h⟩ else 0
        rw [dif_pos j.2]

/-! ### The same with named sources and finite index types -/

/-- the source map of one round -/
def srcOne {r : Round} (e : REnc F E r) {No : Type} (src : No → Ni ⊕ (e.A × ℕ × ℕ)) :
    No → Src Ni [r] (e, PUnit.unit) :=
  fun n => (src n).map id fun q => (.inl q.1, q.2)

/-- the entries of the vectors of one round -/
abbrev REnc.Ent {r : Round} (e : REnc F E r) : Type := Σ a, Fin (e.rows a) × Fin (e.code a).msg

/-- what `name` exposes: the entries of the input and of the vectors sent -/
def rdName {r : Round} (e : REnc F E r) (rdi : Yi → Ni → E) (yo : Yi × r.Orc) : Ni ⊕ e.Ent → E :=
  Sum.elim (rdi yo.1) fun q => e.vecE yo.2 q.1 q.2.1 q.2.2

def srcName {r : Round} (e : REnc F E r) (Ni : Type) : Ni ⊕ e.Ent → Src Ni [r] (e, PUnit.unit) :=
  srcOne e fun n => n.map id fun q => (q.1, q.2.1.val, q.2.2.val)

/-- `name`, with a finite type of exposed entries. -/
theorem Block.tracks_nameFin {r : Round} (e : REnc F E r) (rdi : Yi → Ni → E) :
    (Block.name Xi Yi r).Tracks (e, PUnit.unit) rdi (rdName e rdi) (srcName e Ni) :=
  Block.tracks_one e (fun n : Ni ⊕ e.Ent => n.map id fun q => (q.1, q.2.1.val, q.2.2.val))
      fun y m _ n => by
    cases n with
    | inl k => rfl
    | inr q =>
      show e.vecE m.1 q.1 q.2.1 q.2.2 = nat (fun i' => nat (e.vecE m.1 q.1 i') q.2.2.val) q.2.1.val
      unfold nat
      rw [dif_pos q.2.1.2]
      show _ = if h : q.2.2.val < (e.code q.1).msg then e.vecE m.1 q.1 q.2.1 ⟨q.2.2.val, h⟩ else 0
      rw [dif_pos q.2.2.2]

def srcSame {r : Round} (e : REnc F E r) (Ni : Type) : Ni → Src Ni [r] (e, PUnit.unit) :=
  srcOne e fun n => Sum.inl n

/-- `sample`, with the source `srcSame`. -/
theorem Block.tracks_sample'
    {C : Type} [Fintype C] [Nonempty C] (ok : C → Bool) (rdi : Yi → Ni → E) :
    (Block.sample Xi Yi E C ok).Tracks
      (REnc.none E F Empty C, PUnit.unit) rdi rdi (srcSame (REnc.none E F Empty C) Ni) :=
  Block.tracks_sample ok rdi

/-- the encoding data of a pad vector -/
abbrev REnc.pad (E : Type) [Field E] [Algebra F E] (C : Code.Enc F) [Nonempty (Fin C.n)] (q : ℕ) :
    REnc F E (Block.padRound E C.msg) :=
  REnc.ofV E Unit (fun _ => C) (fun _ => 1) (fun _ => 0) (fun _ => Role.pad) (fun _ => q) Empty Unit

def srcPads (C : Code.Enc F) [Nonempty (Fin C.n)] (q : ℕ) (Ni : Type) :
    Ni ⊕ Fin C.msg → Src Ni [Block.padRound E C.msg] (REnc.pad E C q, PUnit.unit) :=
  srcOne (REnc.pad E C q) fun n => n.map id fun j => ((), 0, j.val)

/-- `pads`, with the source `srcPads`. -/
theorem Block.tracks_pads' (C : Code.Enc F) [Nonempty (Fin C.n)] (q : ℕ) (rdi : Yi → Ni → E) :
    (Block.pads Xi Yi E C.msg).Tracks
      (REnc.pad E C q, PUnit.unit) rdi (fun yo => Sum.elim (rdi yo.1) yo.2) (srcPads C q Ni) :=
  Block.tracks_pads C q rdi

end Lib
end Blocks
