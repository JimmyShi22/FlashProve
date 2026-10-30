-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
One file of the set on the key file's table of joints (Johnson/Desc/Key/KeyBorders.lean).
Johnson/Desc/Key/KeyKeeps.lean: THE TABLE OF JOINTS OF THE KEY FILE: FROM A ROW's TWO HALVES TO THE PLAIN ROAD's LAW OF A BLOCK: «Keeps» (Johnson/Desc/Plain/Leads.lean:51; what Plain/FoldChain.lean's EachKeeps asks block by block), FOR A BLOCK WHOSE LAW HAS NO ERROR TERM:
what holds for certain of whatever the verifier puts out costs nothing (Leads.of_sure). General in the state, in the readers and in the piece. General in the promise's last letter «free» too (where ties that are no Bool stand), in front and behind.
  onB | relB | claimB   the table's promise, relation and claim at a border, as functions of the rule's statement ((what was handed, the chain's state), the oracles): KeyRows1At's on₁ | R₁ | L₁ are these at shape₁ k and open₁ n k
  out_behind'           the strings of the statement behind a piece are what its stage leaves: SendLaw.out_behind, ITS THREE LINES TYPED AGAIN so that its file's imports are not drawn in
  strsStay_of_out       **PROVED**: where a piece puts out b: StrsStay O at the strings in front and behind, PROVIDED every message whose pin is open in O lies in a tree that was sent in front of the piece (cellStays | wordStays)
  keeps_of_halves       **PROVED**: the promise's half and the claim's half, each at the block's own decide's yes ⟹ Keeps, at ANY list of errors
  emptyRow_keeps        **PROVED**: AN EMPTY ROW: from: the block leaves what was handed · KeyQuiet.Rides' facts · the book-keeping's step
  rngRows_keeps         **PROVED**: rng.0.rows' ROW: from the same and KeyLaws.RowsLaidFacts
WHAT IS OWED FOR EACH BLOCK: the facts at its decide's yes: equations on the state (the state's files' readers) · that the pinned messages' trees lie below the piece's base (the tiling's numbers) · coll reads the stored table's cells alone.
EMPTY WHERE: the promise holds of nothing · the block refuses all. An honest run shows the book-keeping's Bool true at each border and the facts on the readers true around each block; it shows no witness.
Nothing on soundness.
-/
import Johnson.Desc.Key.KeyQuiet
import Johnson.Desc.Sound.StringsStay
import Johnson.Desc.Plain.PieceYes

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Key
open OnBytes
open VerifiableInference.Desc.Sound VerifiableInference.Desc.Plain
open OnBytes.Maker OnBytes.Flat KObj
open _root_.Run.PQ (CK)
open _root_.Iop (Reduction)

section
variable {XI P S Cells M Smp Rec Cl W : Type} {C : CK} (F : FileDescription XI) (Fr : Frame) (G : Reading (P × S) Cells M Smp Rec) (at_ : Where)
  (Mg : KMeaning P S (Wit Cells Unit M))

/-- The promise at a border, of the rule's statement. -/
def onB (shape : S → Bool) (free : P × S → Strs → Prop) (O : List KItem) (x : (P × S) × Fr.E.Str) : Prop := onAt F G at_ Mg shape free O x.1 (strsOf Fr x.2)

/-- The relation there. -/
def relB (O : List KItem) (x : (P × S) × Fr.E.Str) (w : Wit Cells Unit M) : Prop := relAt F G at_ Mg O x.1 (strsOf Fr x.2) w

/-- The claim there: there is a witness. -/
def claimB (O : List KItem) (x : (P × S) × Fr.E.Str) : Prop := ∃ w, relB F Fr G at_ Mg O x w

/-- SendLaw.out_behind (Johnson/Desc/Sound/SendLaw.lean), typed again (see the head). -/
theorem out_behind' (pc : Piece C Fr (P × S) Cl W) (a b : (P × S) × Fr.E.Str) (τ : Iop.Tr (uLT C pc.ds))
    (h : pc.ior.red.out a τ = some b) : b.2 = behind C Fr pc.base pc.ds a.2 τ := by
  have h' : (pc.ior.out a.1 a.2 τ).map (fun x => (x, pc.ior.imp a.2 τ)) = some b := h
  obtain ⟨x, -, rfl⟩ := Option.map_eq_some_iff.1 h'
  rfl

theorem strsStay_of_out (pc : Piece C Fr (P × S) Cl W) (O : List KItem) (hbase : ∀ k ∈ pinned O, (at_ k).1 < pc.base)
    (a b : (P × S) × Fr.E.Str) (τ : Iop.Tr (uLT C pc.ds)) (h : pc.ior.red.out a τ = some b) : StrsStay F at_ O (strsOf Fr a.2) (strsOf Fr b.2) := by
  rw [out_behind' Fr pc a b τ h]
  exact ⟨funext fun x => cellStays C Fr pc.base pc.ds a.2 τ x, fun k hk => wordStays XI F C Fr pc.base pc.ds a.2 τ _ _ (hbase k hk)⟩

/-- **From the two halves to the plain road's law.** -/
theorem keeps_of_halves (pc : Piece C Fr (P × S) Cl W) (shape shape' : S → Bool) (free free' : P × S → Strs → Prop) (O O' : List KItem) (hbase : ∀ k ∈ pinned O, (at_ k).1 < pc.base)
    (fwd : ∀ a rs gs b y y', pc.b.decide a rs gs = .ok b → StrsStay F at_ O y y' → onAt F G at_ Mg shape free O a y → onAt F G at_ Mg shape' free' O' b y')
    (back : ∀ a rs gs b y y' w, pc.b.decide a rs gs = .ok b → StrsStay F at_ O y y' → onAt F G at_ Mg shape free O a y → relAt F G at_ Mg O' b y' w → relAt F G at_ Mg O a y w) :
    pc.ior.red.Keeps (onB F Fr G at_ Mg shape free O) (onB F Fr G at_ Mg shape' free' O') (claimB F Fr G at_ Mg O) (claimB F Fr G at_ Mg O') pc.err := by
  unfold Reduction.Keeps
  refine Reduction.Leads.of_sure (K := pc.ior.red) pc.err fun a τ b ha hb => ?_
  have hd := piece_decides_at pc a τ b hb
  have Hy := strsStay_of_out F Fr at_ pc O hbase a b τ hb
  exact ⟨fwd a.1 _ _ b.1 _ _ hd Hy ha, fun ⟨w, hw⟩ => ⟨w, back a.1 _ _ b.1 _ _ w hd Hy ha hw⟩⟩

end

theorem pinned_mono (O₂ O : List KItem) (h : ∀ i ∈ O₂, i ∈ O) (k : Nat) (hk : k ∈ pinned O₂) : k ∈ pinned O := by
  obtain ⟨i, hi, e⟩ := List.mem_filterMap.1 hk
  exact List.mem_filterMap.2 ⟨i, h i hi, e⟩

section
variable {XI P S Cells M Smp Rec Cl W : Type} {C : CK} (F : FileDescription XI) (Fr : Frame) (G : Reading (P × S) Cells M Smp Rec) (at_ : Where)
  (K : KPlan) (R : KRead Cells M) (X : KReaders S)
  (near : Nat → P × S → Strs → Prop) (forms worth other : Nat → String → P × S → Strs → Wit Cells Unit M → Prop)

local notation "Mg" => meaning₁ K R X near forms worth other

/-- **An empty row's law.** -/
theorem emptyRow_keeps (pc : Piece C Fr (P × S) Cl W) (shape shape' : S → Bool) (free free' : P × S → Strs → Prop) (O : List KItem) (hO : ∀ i ∈ O, plain i = true) (hbase : ∀ k ∈ pinned O, (at_ k).1 < pc.base)
    (hdec : ∀ a rs gs b, pc.b.decide a rs gs = .ok b → b.1 = a.1 ∧ Rides G X O a.1 a.2 b.2 ∧ (shape a.2 = true → shape' b.2 = true) ∧
      ∀ y y', StrsStay F at_ O y y' → free a y → free' b y') :
    pc.ior.red.Keeps (onB F Fr G at_ (Mg) shape free O) (onB F Fr G at_ (Mg) shape' free' O) (claimB F Fr G at_ (Mg) O) (claimB F Fr G at_ (Mg) O) pc.err := by
  refine keeps_of_halves F Fr G at_ (Mg) pc shape shape' free free' O O hbase ?_ ?_
  · rintro ⟨p, s⟩ rs gs ⟨p', s'⟩ y y' hd Hy ha
    obtain ⟨e, Hr, hs, hf⟩ := hdec _ rs gs _ hd
    have e' : p' = p := e
    subst e'
    exact onAt_fwd F G at_ K R X near forms worth other shape shape' free free' O O rfl p' s s' y y' Hr.marked Hr.pins Hy (hf y y' Hy) hs ha
  · rintro ⟨p, s⟩ rs gs ⟨p', s'⟩ y y' w hd Hy _ hw
    obtain ⟨e, Hr, _, _⟩ := hdec _ rs gs _ hd
    have e' : p' = p := e
    subst e'
    exact emptyRow_back F G at_ K R X near forms worth other O hO p' s s' y y' w Hr Hy hw

theorem shape_of_on (hm : ∀ s, X.marked s = false) (shape : S → Bool) (free : P × S → Strs → Prop) (O : List KItem) (a : P × S) (y : Strs)
    (h : onAt F G at_ (Mg) shape free O a y) : shape a.2 = true :=
  h.elim (fun hn => absurd (hm a.2) hn) (·.1)

/-- **rng.0.rows' row's law.** r: the table's row there, said by its three lists. The promise's book-keeping is handed to the block's facts. -/
theorem rngRows_keeps (pc : Piece C Fr (P × S) Cl W) (shape shape' : S → Bool) (free free' : P × S → Strs → Prop) (n : Nat) (r : KRow)
    (hins : r.ins = (List.range n).map KItem.rows ++ [.srow 1]) (houts : r.outs = [.grows]) (hctx : r.ctx = [.pin 1])
    (O : List KItem) (hO : ∀ i ∈ O, plain i = true) (hpin : KItem.pin 1 ∈ O) (hpins : pinned (stepOpen O r) = pinned O) (hbase : ∀ k ∈ pinned O, (at_ k).1 < pc.base)
    (hm : ∀ s, X.marked s = false)
    (hdec : ∀ a rs gs b, pc.b.decide a rs gs = .ok b → shape a.2 = true →
      b.1 = a.1 ∧ Rides G X (O.filter fun i => !r.ins.contains i) a.1 a.2 b.2 ∧ RowsLaidFacts K X n a.2 b.2 ∧ shape' b.2 = true ∧ ∀ y y', StrsStay F at_ O y y' → free a y → free' b y') :
    pc.ior.red.Keeps (onB F Fr G at_ (Mg) shape free O) (onB F Fr G at_ (Mg) shape' free' (stepOpen O r)) (claimB F Fr G at_ (Mg) O) (claimB F Fr G at_ (Mg) (stepOpen O r)) pc.err := by
  refine keeps_of_halves F Fr G at_ (Mg) pc shape shape' free free' O (stepOpen O r) hbase ?_ ?_
  · rintro ⟨p, s⟩ rs gs ⟨p', s'⟩ y y' hd Hy ha
    obtain ⟨e, Hr, _, hs, hf⟩ := hdec _ rs gs _ hd (shape_of_on F G at_ K R X near forms worth other hm shape free O _ y ha)
    have e' : p' = p := e
    subst e'
    exact onAt_fwd F G at_ K R X near forms worth other shape shape' free free' O (stepOpen O r) hpins p' s s' y y' Hr.marked Hr.pins Hy (hf y y' Hy) (fun _ => hs) ha
  · rintro ⟨p, s⟩ rs gs ⟨p', s'⟩ y y' w hd Hy ha hw
    obtain ⟨e, Hr, Hf, _, _⟩ := hdec _ rs gs _ hd (shape_of_on F G at_ K R X near forms worth other hm shape free O _ y ha)
    have e' : p' = p := e
    subst e'
    exact rngRows_back F G at_ K R X near forms worth other n r hins houts hctx O hO hpin p' s s' y y' w Hf Hr
      ⟨Hy.cell, fun k hk => Hy.word k (pinned_mono _ O (fun i hi => (List.mem_filter.1 hi).1) k hk)⟩ hw

end

end VerifiableInference.Desc.Key

#print axioms VerifiableInference.Desc.Key.keeps_of_halves
#print axioms VerifiableInference.Desc.Key.emptyRow_keeps
#print axioms VerifiableInference.Desc.Key.rngRows_keeps
