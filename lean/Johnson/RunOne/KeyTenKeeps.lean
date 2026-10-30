-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
One file of the set on the key file's table of joints (Johnson/Desc/Key/KeyBorders.lean).
Johnson/RunOne/KeyTenKeeps.lean: THE KEY FILE's FIRST CHAIN AT THE FROZEN F_K: THE PLAIN ROAD's LAW «Keeps» (Johnson/Desc/Plain/Leads.lean:51), AT THE TABLE OF JOINTS' OWN on₁ | L₁ (Johnson/RunOne/KeyRows1At.lean), FOR THE BLOCKS WITHOUT A ROUND: entries of Plain/FoldChain.lean's
EachKeeps along the row that piecesAt holds: each piece's block is «held b» (below b, lifted to the pair of what was handed and the chain's state; Johnson/Desc/Sound/PaidAtDesc.lean:28).
free₁'s fence on the rows' content rides. OVER Johnson/Desc/Key/KeyShape.lean AND KeyRows1At.lean (the promise holds the ties: the Bool ones in shape₁, the others in free₁; the number of lookups among them: NO PREMISE n₁ one = 2). SEVEN OF THE TEN: look0 | look1: laid · behind the batching · cleared · THE SEAL: borders 2→3 · 6→7 · 7→8 · 8→9 · 12→13 · 13→14 · 18→19. AT ANY LIST OF ERRORS (a block without a round has none to spend).
  Held pc b        the piece's block's yes at (x, s) hands on x and is b's yes at s: held_decide (Johnson/Desc/Plain/PaidKeeps.lean) pays it at pc.b = held b
  CollCell coll    «collision» reads of the oracles the stored table's cells alone
  keeps_empty_at   an empty row at border k, from the block's facts
  keeps_laid0 | behind0 | cleared0 | laid1 | behind1 | cleared1 | keeps_seal   **PROVED**
WHAT EACH STILL ASKS, BY NAME: Held · that b's decide is the link's own text (by unfolding Link.blocksInOrder at firstChain) · every message whose pin is open lies in a tree sent in front of the piece (the tiling's numbers) · CollCell ·
for «cleared»: ReadsD (the reading reads of the state the statement's part alone).
EMPTY WHERE on₁ k HOLDS OF NOTHING: BY RUNS, AT BOTH SIZES (forecasts written down beforehand; no miss), at the honest file's state at border k: the book-keeping's Bool WITH ALL THE TIES (shape₁ of KeyShape.lean in the build of these runs, at KeyReaders1.ties₁ := tiesA && moreB && sizesB) is true at all twenty borders; ELEVEN CONTROLS ON THE BOOL, each no just where due: idx read one higher · the rider struck · the next border's counts at a state · the claim's masks struck · g's vectors made not ok · lin.w one higher · the mark «at the end» struck · a list of keys more · a list of rows more · own := noId · the ranges' group's test read as not begun. NOT TURNED BY ANY CONTROL: the codes' tie · «members just [1]» · «message 2 unsampled, unspent» · «w ≠ noId» by itself · the emptiness at 0 | 1 · «places = messages» · the two static clauses;
 the book's places are stable; EvalIs holds with «the same row» in equality's place at 18 | 19; SampleIn | OpenIn hold through Bools whose yes gives the Prop by theorem (KeyFenceB). The rest of the promise (no collision; NoColl; hasSmp; ArrOk; ReadsPinned; Placed against at_) stands over letters that are not filled.
Nothing on soundness.
-/
import Johnson.Desc.Key.KeyKeeps
import Johnson.RunOne.KeyTen
import Johnson.RunOne.KeyRows1At

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.RunOne.KeyRows1
open OnBytes OnBytes.Params
open VerifiableInference.Desc VerifiableInference.Desc.Key VerifiableInference.Desc.Sound VerifiableInference.Desc.Plain
open VerifiableInference.Desc.Key (FirstState Claim Lookup)
open VerifiableInference.Desc.Key (Xi)
open _root_.Run.PQ (CK)
open _root_.Iop (Reduction)

variable {XI Cells M Smp Rec W : Type} {C : CK} (F : FileDescription XI) (Fr : Frame) (G : Reading (Xi × FirstState) Cells M Smp Rec) (at_ : Where)
  (one : OneTime) (R : KRead Cells M) (coll : Strs → Rec → Prop)

/-- The piece's block's yes hands on what was handed and is b's yes at the chain's state. -/
def Held (pc : Piece C Fr (Xi × FirstState) Claim W) (b : Block FirstState Claim) : Prop :=
  ∀ a rs gs a', pc.b.decide a rs gs = .ok a' → a'.1 = a.1 ∧ b.decide a.2 rs gs = .ok a'.2

/-- «Collision» reads of the oracles the stored table's cells alone. -/
def CollCell {Rec : Type} (coll : Strs → Rec → Prop) : Prop := ∀ y y' r, y'.cell = y.cell → coll y' r → coll y r

/-- **The promise's last letter rides** across a block that turns neither the reading's letters nor the book, between two borders with the same pins. -/
theorem free₁_step (k k' : Nat) (p : Xi) (s s' : FirstState) (y y' : Strs) (hP : SamePins G (p, s) (p, s')) (hcoll : CollCell coll) (Hy : StrsStay F at_ (open₁ 2 k) y y') (hbook : s'.d.book = s.d.book)
    (hpin : pinned (open₁ 2 k') = pinned (open₁ 2 k)) (hk : (2 ≤ k' ∧ k' ≤ 15 → 2 ≤ k ∧ k ≤ 15) ∧ (18 ≤ k' → 18 ≤ k)) (hE : 18 ≤ k' → 18 ≤ k ∧ (KeyRows23.EvalIs one.lin s → KeyRows23.EvalIs one.lin s') ∧ (KeyRows23.OpenIn s.d.st (s.d.st.groups.size - 1) → KeyRows23.OpenIn s'.d.st (s'.d.st.groups.size - 1)))
    (hS : ∀ o, KeyRows23.SampleIn s.d.st o → KeyRows23.SampleIn s'.d.st o) (hO : Means.InOrder s.d.st → Means.InOrder s'.d.st)
    (h : free₁ F G at_ one R coll k (p, s) y) : free₁ F G at_ one R coll k' (p, s') y' := by
  refine ⟨freeAt_fwd G coll p s s' y y' hP (fun r => hcoll y y' r Hy.cell) h.1, h.2.1, ?_, fun h18 => (hE h18).2.1 (h.2.2.2.1 (hE h18).1),
    fun j hj o ho => hS o (h.2.2.2.2.1 j (hpin ▸ hj) o ho), fun h18 => (hE h18).2.2 (h.2.2.2.2.2.1 (hE h18).1), hO h.2.2.2.2.2.2.1,
    fun j hj => shownAt_ride F at_ j y y' (Hy.word j (hpin ▸ hj)) (h.2.2.2.2.2.2.2.1 j (hpin ▸ hj)), h.2.2.2.2.2.2.2.2.1,
    fun hb => by
      show MaskWith (fun o => s'.d.book.place[o]?) 1 2
      rw [hbook]
      exact h.2.2.2.2.2.2.2.2.2.1 (hk.1 hb),
    fun h18 o ho => by
      show MaskWith (fun o => s'.d.book.place[o]?) o (o + 1)
      rw [hbook]
      exact h.2.2.2.2.2.2.2.2.2.2 (hk.2 h18) o ho⟩
  rw [hpin]
  exact h.2.2.1.congr fun o => by
    show s'.d.book.place[o]? = s.d.book.place[o]?
    rw [hbook]

/-- An empty row at border k, where the number of lookups is given. -/
theorem keeps_empty_two (pc : Piece C Fr (Xi × FirstState) Claim W) (b : Block FirstState Claim) (hheld : Held Fr pc b) (k : Nat) (hn : n₁ one = 2)
    (hopen : open₁ 2 (k + 1) = open₁ 2 k) (hplain : ∀ i ∈ open₁ 2 k, plain i = true) (hbase : ∀ j ∈ pinned (open₁ 2 k), (at_ j).1 < pc.base) (hcoll : CollCell coll)
    (hdec : ∀ s rs gs s', b.decide s rs gs = .ok s' → (∀ p, Rides G (readers₁ one) (open₁ 2 k) p s s') ∧ (shape₁ (plan₁ one) (readers₁ one) (book₁ one) 2 (slots₁ one) k s = true → shape₁ (plan₁ one) (readers₁ one) (book₁ one) 2 (slots₁ one) (k + 1) s' = true) ∧
      s'.d.book = s.d.book ∧ (18 ≤ k + 1 → 18 ≤ k ∧ (KeyRows23.EvalIs one.lin s → KeyRows23.EvalIs one.lin s') ∧ (KeyRows23.OpenIn s.d.st (s.d.st.groups.size - 1) → KeyRows23.OpenIn s'.d.st (s'.d.st.groups.size - 1))) ∧
      (∀ o, KeyRows23.SampleIn s.d.st o → KeyRows23.SampleIn s'.d.st o) ∧ (Means.InOrder s.d.st → Means.InOrder s'.d.st))
    (hk : (2 ≤ k + 1 ∧ k + 1 ≤ 15 → 2 ≤ k ∧ k ≤ 15) ∧ (18 ≤ k + 1 → 18 ≤ k) := by omega) :
    pc.ior.red.Keeps (on₁ F Fr G at_ one R coll k) (on₁ F Fr G at_ one R coll (k + 1)) (L₁ F Fr G at_ one R k) (L₁ F Fr G at_ one R (k + 1)) pc.err := by
  have key := emptyRow_keeps F Fr G at_ (plan₁ one) R (readers₁ one) (fun _ _ _ => False) (formsAt (plan₁ one) R k3At₁ one.ranges) (worthAt (plan₁ one) R k3At₁ one.ranges one.codes)
    (fun _ _ _ _ _ => False) pc (shape₁ (plan₁ one) (readers₁ one) (book₁ one) 2 (slots₁ one) k) (shape₁ (plan₁ one) (readers₁ one) (book₁ one) 2 (slots₁ one) (k + 1)) (free₁ F G at_ one R coll k) (free₁ F G at_ one R coll (k + 1)) (open₁ 2 k) hplain hbase
    (fun a rs gs a' h => by
      obtain ⟨e, hb⟩ := hheld a rs gs a' h
      obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hdec _ rs gs _ hb
      refine ⟨e, h1 a.1, h2, fun y y' Hy hf => ?_⟩
      obtain ⟨p, s⟩ := a
      obtain ⟨p', s'⟩ := a'
      have e' : p' = p := e
      subst e'
      exact free₁_step F G at_ one R coll k (k + 1) p' s s' y y' (h1 p').pins hcoll Hy h3 (by rw [hopen]) hk h4 h5 h6 hf)
  unfold on₁ L₁ R₁
  rw [hn, hopen]
  exact key

/-- **An empty row at border k.** THE NUMBER OF LOOKUPS IS NO PREMISE: the promise in front holds it (on₁_two). -/
theorem keeps_empty_at (pc : Piece C Fr (Xi × FirstState) Claim W) (b : Block FirstState Claim) (hheld : Held Fr pc b) (k : Nat)
    (hopen : open₁ 2 (k + 1) = open₁ 2 k) (hplain : ∀ i ∈ open₁ 2 k, plain i = true) (hbase : ∀ j ∈ pinned (open₁ 2 k), (at_ j).1 < pc.base) (hcoll : CollCell coll)
    (hdec : ∀ s rs gs s', b.decide s rs gs = .ok s' → (∀ p, Rides G (readers₁ one) (open₁ 2 k) p s s') ∧ (shape₁ (plan₁ one) (readers₁ one) (book₁ one) 2 (slots₁ one) k s = true → shape₁ (plan₁ one) (readers₁ one) (book₁ one) 2 (slots₁ one) (k + 1) s' = true) ∧
      s'.d.book = s.d.book ∧ (18 ≤ k + 1 → 18 ≤ k ∧ (KeyRows23.EvalIs one.lin s → KeyRows23.EvalIs one.lin s') ∧ (KeyRows23.OpenIn s.d.st (s.d.st.groups.size - 1) → KeyRows23.OpenIn s'.d.st (s'.d.st.groups.size - 1))) ∧
      (∀ o, KeyRows23.SampleIn s.d.st o → KeyRows23.SampleIn s'.d.st o) ∧ (Means.InOrder s.d.st → Means.InOrder s'.d.st))
    (hk : (2 ≤ k + 1 ∧ k + 1 ≤ 15 → 2 ≤ k ∧ k ≤ 15) ∧ (18 ≤ k + 1 → 18 ≤ k) := by omega) :
    pc.ior.red.Keeps (on₁ F Fr G at_ one R coll k) (on₁ F Fr G at_ one R coll (k + 1)) (L₁ F Fr G at_ one R k) (L₁ F Fr G at_ one R (k + 1)) pc.err := by
  intro a ha
  exact keeps_empty_two F Fr G at_ one R coll pc b hheld k (on₁_two F Fr G at_ one R coll k a ha) hopen hplain hbase hcoll hdec hk a ha

section
variable (set : Setting) (i : Nat) (x : Lookup)

/-- Border 2 → 3. -/
theorem keeps_laid0 (pc : Piece C Fr (Xi × FirstState) Claim W) (b : Block FirstState Claim) (hheld : Held Fr pc b) (hb : ∀ s rs gs, b.decide s rs gs = (lookupLink one set i x).lay s)
    (hbase : ∀ j ∈ pinned (open₁ 2 2), (at_ j).1 < pc.base) (hcoll : CollCell coll) :
    pc.ior.red.Keeps (on₁ F Fr G at_ one R coll 2) (on₁ F Fr G at_ one R coll 3) (L₁ F Fr G at_ one R 2) (L₁ F Fr G at_ one R 3) pc.err :=
  keeps_empty_at F Fr G at_ one R coll pc b hheld 2 (by decide) (by decide) hbase hcoll fun s rs gs s' h => by
    have e := lay_ok one set i x s s' ((hb s rs gs).symm.trans h)
    subst e
    exact ⟨fun p => rides_same G one _ p s', sh_2_3 one s', rfl, fun h18 => absurd h18 (by decide), fun _ h => h, fun h => h⟩

/-- Border 6 → 7. -/
theorem keeps_behind0 (pc : Piece C Fr (Xi × FirstState) Claim W) (b : Block FirstState Claim) (hheld : Held Fr pc b) (hb : ∀ s rs gs, b.decide s rs gs = afterIn (lookupLink one set i x).hear (lookupLink one set i x).orderAfter s)
    (hbase : ∀ j ∈ pinned (open₁ 2 6), (at_ j).1 < pc.base) (hcoll : CollCell coll) :
    pc.ior.red.Keeps (on₁ F Fr G at_ one R coll 6) (on₁ F Fr G at_ one R coll 7) (L₁ F Fr G at_ one R 6) (L₁ F Fr G at_ one R 7) pc.err :=
  keeps_empty_at F Fr G at_ one R coll pc b hheld 6 (by decide) (by decide) hbase hcoll fun s rs gs s' h => by
    have e := after_ok one set i x s s' ((hb s rs gs).symm.trans h)
    subst e
    exact ⟨fun p => rides_same G one _ p s', sh_6_7 one s', rfl, fun h18 => absurd h18 (by decide), fun _ h => h, fun h => h⟩

/-- Border 7 → 8. -/
theorem keeps_cleared0 (pc : Piece C Fr (Xi × FirstState) Claim W) (b : Block FirstState Claim) (hheld : Held Fr pc b) (hb : ∀ s rs gs, b.decide s rs gs = (lookupLink one set i x).clear s)
    (hbase : ∀ j ∈ pinned (open₁ 2 7), (at_ j).1 < pc.base) (hcoll : CollCell coll) (hG : ReadsD G) :
    pc.ior.red.Keeps (on₁ F Fr G at_ one R coll 7) (on₁ F Fr G at_ one R coll 8) (L₁ F Fr G at_ one R 7) (L₁ F Fr G at_ one R 8) pc.err :=
  keeps_empty_at F Fr G at_ one R coll pc b hheld 7 (by decide) (by decide) hbase hcoll fun s rs gs s' h => by
    have e := clear_ok one set i x s s' ((hb s rs gs).symm.trans h)
    subst e
    exact ⟨fun p => rides_clr G one hG _ p s, sh_7_8 one s, rfl, fun h18 => absurd h18 (by decide), fun _ h => h, fun h => h⟩

/-- Border 8 → 9. -/
theorem keeps_laid1 (pc : Piece C Fr (Xi × FirstState) Claim W) (b : Block FirstState Claim) (hheld : Held Fr pc b) (hb : ∀ s rs gs, b.decide s rs gs = (lookupLink one set i x).lay s)
    (hbase : ∀ j ∈ pinned (open₁ 2 8), (at_ j).1 < pc.base) (hcoll : CollCell coll) :
    pc.ior.red.Keeps (on₁ F Fr G at_ one R coll 8) (on₁ F Fr G at_ one R coll 9) (L₁ F Fr G at_ one R 8) (L₁ F Fr G at_ one R 9) pc.err :=
  keeps_empty_at F Fr G at_ one R coll pc b hheld 8 (by decide) (by decide) hbase hcoll fun s rs gs s' h => by
    have e := lay_ok one set i x s s' ((hb s rs gs).symm.trans h)
    subst e
    exact ⟨fun p => rides_same G one _ p s', sh_8_9 one s', rfl, fun h18 => absurd h18 (by decide), fun _ h => h, fun h => h⟩

/-- Border 12 → 13. -/
theorem keeps_behind1 (pc : Piece C Fr (Xi × FirstState) Claim W) (b : Block FirstState Claim) (hheld : Held Fr pc b) (hb : ∀ s rs gs, b.decide s rs gs = afterIn (lookupLink one set i x).hear (lookupLink one set i x).orderAfter s)
    (hbase : ∀ j ∈ pinned (open₁ 2 12), (at_ j).1 < pc.base) (hcoll : CollCell coll) :
    pc.ior.red.Keeps (on₁ F Fr G at_ one R coll 12) (on₁ F Fr G at_ one R coll 13) (L₁ F Fr G at_ one R 12) (L₁ F Fr G at_ one R 13) pc.err :=
  keeps_empty_at F Fr G at_ one R coll pc b hheld 12 (by decide) (by decide) hbase hcoll fun s rs gs s' h => by
    have e := after_ok one set i x s s' ((hb s rs gs).symm.trans h)
    subst e
    exact ⟨fun p => rides_same G one _ p s', sh_12_13 one s', rfl, fun h18 => absurd h18 (by decide), fun _ h => h, fun h => h⟩

/-- Border 13 → 14. -/
theorem keeps_cleared1 (pc : Piece C Fr (Xi × FirstState) Claim W) (b : Block FirstState Claim) (hheld : Held Fr pc b) (hb : ∀ s rs gs, b.decide s rs gs = (lookupLink one set i x).clear s)
    (hbase : ∀ j ∈ pinned (open₁ 2 13), (at_ j).1 < pc.base) (hcoll : CollCell coll) (hG : ReadsD G) :
    pc.ior.red.Keeps (on₁ F Fr G at_ one R coll 13) (on₁ F Fr G at_ one R coll 14) (L₁ F Fr G at_ one R 13) (L₁ F Fr G at_ one R 14) pc.err :=
  keeps_empty_at F Fr G at_ one R coll pc b hheld 13 (by decide) (by decide) hbase hcoll fun s rs gs s' h => by
    have e := clear_ok one set i x s s' ((hb s rs gs).symm.trans h)
    subst e
    exact ⟨fun p => rides_clr G one hG _ p s, sh_13_14 one s, rfl, fun h18 => absurd h18 (by decide), fun _ h => h, fun h => h⟩

end

/-- Border 18 → 19: THE SEAL. asks: the chain's own clauses on its carried record, whatever they are. -/
theorem keeps_seal (pc : Piece C Fr (Xi × FirstState) Claim W) (b : Block FirstState Claim) (hheld : Held Fr pc b) (asks : FirstState → ChainEnd.Clauses)
    (hb : ∀ s rs gs, b.decide s rs gs = (ChainEnd.refuse (asks s)).map fun _ => s)
    (hbase : ∀ j ∈ pinned (open₁ 2 18), (at_ j).1 < pc.base) (hcoll : CollCell coll) :
    pc.ior.red.Keeps (on₁ F Fr G at_ one R coll 18) (on₁ F Fr G at_ one R coll 19) (L₁ F Fr G at_ one R 18) (L₁ F Fr G at_ one R 19) pc.err :=
  keeps_empty_at F Fr G at_ one R coll pc b hheld 18 (by decide) (by decide) hbase hcoll fun s rs gs s' h => by
    have e := seal_ok asks s s' ((hb s rs gs).symm.trans h)
    subst e
    exact ⟨fun p => rides_same G one _ p s', sh_18_19 one s', rfl, fun _ => ⟨by decide, id, id⟩, fun _ h => h, fun h => h⟩

end Johnson.RunOne.KeyRows1

#print axioms Johnson.RunOne.KeyRows1.keeps_laid0
#print axioms Johnson.RunOne.KeyRows1.keeps_behind0
#print axioms Johnson.RunOne.KeyRows1.keeps_cleared0
#print axioms Johnson.RunOne.KeyRows1.keeps_laid1
#print axioms Johnson.RunOne.KeyRows1.keeps_behind1
#print axioms Johnson.RunOne.KeyRows1.keeps_cleared1
#print axioms Johnson.RunOne.KeyRows1.keeps_seal
