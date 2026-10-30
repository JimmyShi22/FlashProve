-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
One file of the set on the key file's table of joints (Johnson/Desc/Key/KeyBorders.lean).
Johnson/RunOne/KeyTenAt.lean (over the promise with the ties: Johnson/Desc/Key/KeyShape.lean · Johnson/RunOne/KeyRows1At.lean · Johnson/RunOne/KeyReaders1.lean; flat_length: «19» IS A THEOREM under hl and hw · finD_of_shape: the file's last test's part on chain 1's last state follows from border 19's book-keeping): ALL TEN: THE SEVEN Keeps OF Johnson/RunOne/KeyTenKeeps.lean, rng.0.rows' (KeyThree) AND THE TWO CALLERS' (KeyCaller), WITH THEIR «YES» FACTS PAID (KeyYes), AT THE FROZEN CHAIN's OWN BLOCKS: «the k-th block of (firstChain one D told set N).blocksInOrder, held» (the row that piecesAt holds): three of their named premises are paid here:
  Held        by held_decide (Johnson/Desc/Plain/PaidKeeps.lean) at pc.b = held b
  hb          by unfolding Chain.blocksInOrder | Link.blocksInOrder | endAt at firstChain, UNDER hl : the plan has just two lookups (lookupsOf one = [x₀, x₁]); for the seal besides hw : the shape has a message with W
  (n₁ one = 2 is no premise of the ten: the promise holds it)
WHAT IS LEFT, BY NAME, FOR ALL TEN: hl (| hw): evaluated at both sizes' public files · hbase (the tiling's numbers against the letter at_) · CollCell · ReadsL (at «cleared» · rng.0.rows · the callers: ONE premise on the reading).
Nothing on soundness.
-/
import Johnson.RunOne.KeyYes
import Johnson.Desc.Plain.PaidKeeps

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.RunOne.KeyRows1
open OnBytes OnBytes.Params
open VerifiableInference.Desc VerifiableInference.Desc.Key VerifiableInference.Desc.Sound VerifiableInference.Desc.Plain
open VerifiableInference.Desc.Key (FirstState Claim Lookup)
open VerifiableInference.Desc.Key (Xi)
open _root_.Run.PQ (CK)
open _root_.Iop (Reduction)

theorem n₁_two (one : OneTime) (x₀ x₁ : Lookup) (hl : lookupsOf one = [x₀, x₁]) : n₁ one = 2 := by
  unfold n₁; rw [hl]; rfl

theorem held_of {C : CK} {W : Type} (Fr : Frame) (pc : Piece C Fr (Xi × FirstState) Claim W) (b : Block FirstState Claim) (hpc : pc.b = held b) : Held Fr pc b := by
  intro a rs gs a' h
  rw [hpc] at h
  exact held_decide b a rs gs a' h

section
variable (one : OneTime) (D : List Fmt.DeclaredRound) (told : List ProofFile.Root) (set : Setting) (N : H2U.PlaceNums) (x₀ x₁ : Lookup)

theorem dec_laid0 (hl : lookupsOf one = [x₀, x₁]) (b : Block FirstState Claim) (h : (firstChain one D told set N).blocksInOrder[2]? = some b) (s : FirstState) (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64))) :
    b.decide s rs gs = (lookupLink one set 0 x₀).lay s := by
  simp only [firstChain, hl] at h
  have e : _ = b := Option.some.inj h
  subst e
  rfl

theorem dec_behind0 (hl : lookupsOf one = [x₀, x₁]) (b : Block FirstState Claim) (h : (firstChain one D told set N).blocksInOrder[6]? = some b) (s : FirstState) (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64))) :
    b.decide s rs gs = afterIn (lookupLink one set 0 x₀).hear (lookupLink one set 0 x₀).orderAfter s := by
  simp only [firstChain, hl] at h
  have e : _ = b := Option.some.inj h
  subst e
  rfl

theorem dec_cleared0 (hl : lookupsOf one = [x₀, x₁]) (b : Block FirstState Claim) (h : (firstChain one D told set N).blocksInOrder[7]? = some b) (s : FirstState) (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64))) :
    b.decide s rs gs = (lookupLink one set 0 x₀).clear s := by
  simp only [firstChain, hl] at h
  have e : _ = b := Option.some.inj h
  subst e
  rfl

theorem dec_laid1 (hl : lookupsOf one = [x₀, x₁]) (b : Block FirstState Claim) (h : (firstChain one D told set N).blocksInOrder[8]? = some b) (s : FirstState) (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64))) :
    b.decide s rs gs = (lookupLink one set 1 x₁).lay s := by
  simp only [firstChain, hl] at h
  have e : _ = b := Option.some.inj h
  subst e
  rfl

theorem dec_behind1 (hl : lookupsOf one = [x₀, x₁]) (b : Block FirstState Claim) (h : (firstChain one D told set N).blocksInOrder[12]? = some b) (s : FirstState) (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64))) :
    b.decide s rs gs = afterIn (lookupLink one set 1 x₁).hear (lookupLink one set 1 x₁).orderAfter s := by
  simp only [firstChain, hl] at h
  have e : _ = b := Option.some.inj h
  subst e
  rfl

theorem dec_cleared1 (hl : lookupsOf one = [x₀, x₁]) (b : Block FirstState Claim) (h : (firstChain one D told set N).blocksInOrder[13]? = some b) (s : FirstState) (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64))) :
    b.decide s rs gs = (lookupLink one set 1 x₁).clear s := by
  simp only [firstChain, hl] at h
  have e : _ = b := Option.some.inj h
  subst e
  rfl

theorem dec_seal (hl : lookupsOf one = [x₀, x₁]) (bw : Block FirstState Claim)
    (hw : sendW one pieces (rootsBefore D (batchRound D)) (groupsTold told (rootsBefore D (lastSendRound D)) (rootsAt D (lastSendRound D))) = some bw)
    (b : Block FirstState Claim) (h : (firstChain one D told set N).blocksInOrder[18]? = some b) :
    ∃ asks : FirstState → ChainEnd.Clauses, ∀ (s : FirstState) (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64))), b.decide s rs gs = (ChainEnd.refuse (asks s)).map fun _ => s := by
  simp only [firstChain, hl, hw] at h
  have e : _ = b := Option.some.inj h
  subst e
  exact ⟨_, fun _ _ _ => rfl⟩

end


theorem slots₁_at (one : OneTime) (x₀ x₁ : Lookup) (hl : lookupsOf one = [x₀, x₁]) : slots₁ one 0 = (K3.faceOfLkp x₀).slots ∧ slots₁ one 1 = (K3.faceOfLkp x₁).slots := by
  unfold slots₁; rw [hl]; exact ⟨rfl, rfl⟩

section
variable (one : OneTime) (D : List Fmt.DeclaredRound) (told : List ProofFile.Root) (set : Setting) (N : H2U.PlaceNums) (x₀ x₁ : Lookup)

/-- **THE FIRST CHAIN HAS NINETEEN BLOCKS**, where the plan's lookups are a list of two and the shape has a message with W. -/
theorem flat_length (hl : lookupsOf one = [x₀, x₁]) (bw : Block FirstState Claim)
    (hw : sendW one pieces (rootsBefore D (batchRound D)) (groupsTold told (rootsBefore D (lastSendRound D)) (rootsAt D (lastSendRound D))) = some bw) :
    (firstChain one D told set N).blocksInOrder.length = 19 := by
  simp only [firstChain, hl, hw]
  rfl

/-- **THE FILE's LAST TEST's PART ON THE FIRST CHAIN's LAST STATE FOLLOWS FROM THE BOOK-KEEPING AT BORDER 19.** -/
theorem finD_of_shape (s : FirstState) (h : shape₁ (plan₁ one) (readers₁ one) (book₁ one) 2 (slots₁ one) 19 s = true) : firstEndOk one s = true := by
  obtain ⟨ht, hc⟩ := (shape₁_iff (plan₁ one) (readers₁ one) (book₁ one) 2 (slots₁ one) 19 s).1 h
  have ht' : (tiesA one 19 s && moreB 19 s && sizesB one 19 s) = true := ht
  obtain ⟨h12, _⟩ := Bool.and_eq_true_iff.1 ht'
  obtain ⟨hA, hM⟩ := Bool.and_eq_true_iff.1 h12
  have hM' : (s.base.rows.length == 2 && s.base.keys.length == 2 && s.atEnd && (s.lin.any fun l => l.own != noId && l.w != noId && l.mask == some (l.w + 1)) &&
    ((s.d.st.groups.toList.drop s.grp).dropLast.all fun G => G.inRun && G.rows.isEmpty) && VerifiableInference.Desc.Sound.bookStepB 0 s.d.book s.d.roots) = true := hM
  simp only [Bool.and_eq_true] at hM'
  obtain ⟨⟨⟨⟨⟨_, m2⟩, m3⟩, m4'⟩, m5⟩, _⟩ := hM'
  have m4 : (s.lin.any fun l => l.own != noId && l.w != noId) = true := by
    cases hL : s.lin with
    | none => rw [hL] at m4'; cases m4'
    | some l =>
      rw [hL] at m4'
      simp only [Option.any_some, Bool.and_eq_true] at m4' ⊢
      exact m4'.1
  have hlen : (lookupsOf one).length = 2 := by
    unfold tiesA at hA
    simp only [Bool.and_eq_true] at hA
    exact beq_iff_eq.1 hA.1.1.1.1
  have hc2 : ((book₁ one).ledger s).isNone = true ∧ groupB (readers₁ one) s true 0 = true := by
    have q : (sentB (plan₁ one) (readers₁ one) s 0 && sentB (plan₁ one) (readers₁ one) s 1 && ((book₁ one).ledger s).isNone && !(book₁ one).heard s && doneB (plan₁ one) (readers₁ one) 2 2 s &&
      (groupB (readers₁ one) s true 0 && ((readers₁ one).pile s).isSome && ((readers₁ one).eval s).isSome && ((readers₁ one).g s).isSome && sentB (plan₁ one) (readers₁ one) s 2 && ownB (plan₁ one) (readers₁ one) (book₁ one) s && (book₁ one).handed s)) = true := hc
    simp only [Bool.and_eq_true] at q
    exact ⟨q.1.1.1.2, q.2.1.1.1.1.1.1⟩
  have hfork : s.base.fork.isNone = true := by
    have q : (s.base.fork.map _).isNone = true := hc2.1
    cases hf : s.base.fork with
    | none => rfl
    | some F => rw [hf] at q; cases q
  obtain ⟨g, Gr, hg, hG, _, _⟩ := groupB_some (readers₁ one) s true 0 hc2.2
  have eg := grp_eq one s g hg
  subst eg
  have hlt : s.grp < s.d.st.groups.size := (Array.getElem?_eq_some_iff.1 (show s.d.st.groups[s.grp]? = some Gr from hG)).1
  show ((s.atEnd && s.lin.any fun l => l.own != noId && l.w != noId) && s.base.fork.isNone && s.base.keys.length == (lookupsOf one).length && decide (s.grp < s.d.st.groups.size) &&
    (((s.d.st.groups.toList.drop s.grp).dropLast).all fun G => G.inRun && G.rows.isEmpty)) = true
  rw [m3, m4, hfork, hlen, m2, decide_eq_true hlt, m5]
  rfl

theorem yes_caller0 (hl : lookupsOf one = [x₀, x₁]) (b : Block FirstState Claim) (h : (firstChain one D told set N).blocksInOrder[3]? = some b) : CallerYes (slots₁ one 0) b := by
  simp only [firstChain, hl] at h
  have e : _ = b := Option.some.inj h
  subst e
  rw [(slots₁_at one x₀ x₁ hl).1]
  exact callerYes one 0 x₀

theorem yes_caller1 (hl : lookupsOf one = [x₀, x₁]) (b : Block FirstState Claim) (h : (firstChain one D told set N).blocksInOrder[9]? = some b) : CallerYes (slots₁ one 1) b := by
  simp only [firstChain, hl] at h
  have e : _ = b := Option.some.inj h
  subst e
  rw [(slots₁_at one x₀ x₁ hl).2]
  exact callerYes one 1 x₁

theorem yes_rngRows (hl : lookupsOf one = [x₀, x₁]) (b : Block FirstState Claim) (h : (firstChain one D told set N).blocksInOrder[14]? = some b) : RowsYes b := by
  have hn : (lookupsOf one).length = 2 := by rw [hl]; rfl
  simp only [firstChain, hl] at h
  have e : _ = b := Option.some.inj h
  subst e
  exact rowsYes one hn

end

section
variable {XI Cells M Smp Rec W : Type} {C : CK} (F : FileDescription XI) (Fr : Frame) (G : Reading (Xi × FirstState) Cells M Smp Rec) (at_ : Where)
  (one : OneTime) (R : KRead Cells M) (coll : Strs → Rec → Prop)
  (D : List Fmt.DeclaredRound) (told : List ProofFile.Root) (set : Setting) (N : H2U.PlaceNums) (x₀ x₁ : Lookup)

/-- Border 2 → 3, at the frozen chain's own block number 2, held. -/
theorem at_laid0 (hl : lookupsOf one = [x₀, x₁]) (b : Block FirstState Claim) (h : (firstChain one D told set N).blocksInOrder[2]? = some b)
    (pc : Piece C Fr (Xi × FirstState) Claim W) (hpc : pc.b = held b) (hbase : ∀ j ∈ pinned (open₁ 2 2), (at_ j).1 < pc.base) (hcoll : CollCell coll) :
    pc.ior.red.Keeps (on₁ F Fr G at_ one R coll 2) (on₁ F Fr G at_ one R coll 3) (L₁ F Fr G at_ one R 2) (L₁ F Fr G at_ one R 3) pc.err :=
  keeps_laid0 F Fr G at_ one R coll set 0 x₀ pc b (held_of Fr pc b hpc) (dec_laid0 one D told set N x₀ x₁ hl b h) hbase hcoll

/-- Border 6 → 7, at the frozen chain's own block number 6, held. -/
theorem at_behind0 (hl : lookupsOf one = [x₀, x₁]) (b : Block FirstState Claim) (h : (firstChain one D told set N).blocksInOrder[6]? = some b)
    (pc : Piece C Fr (Xi × FirstState) Claim W) (hpc : pc.b = held b) (hbase : ∀ j ∈ pinned (open₁ 2 6), (at_ j).1 < pc.base) (hcoll : CollCell coll) :
    pc.ior.red.Keeps (on₁ F Fr G at_ one R coll 6) (on₁ F Fr G at_ one R coll 7) (L₁ F Fr G at_ one R 6) (L₁ F Fr G at_ one R 7) pc.err :=
  keeps_behind0 F Fr G at_ one R coll set 0 x₀ pc b (held_of Fr pc b hpc) (dec_behind0 one D told set N x₀ x₁ hl b h) hbase hcoll

/-- Border 7 → 8, at the frozen chain's own block number 7, held. -/
theorem at_cleared0 (hl : lookupsOf one = [x₀, x₁]) (b : Block FirstState Claim) (h : (firstChain one D told set N).blocksInOrder[7]? = some b)
    (pc : Piece C Fr (Xi × FirstState) Claim W) (hpc : pc.b = held b) (hbase : ∀ j ∈ pinned (open₁ 2 7), (at_ j).1 < pc.base) (hcoll : CollCell coll) (hG : ReadsL G) :
    pc.ior.red.Keeps (on₁ F Fr G at_ one R coll 7) (on₁ F Fr G at_ one R coll 8) (L₁ F Fr G at_ one R 7) (L₁ F Fr G at_ one R 8) pc.err :=
  keeps_cleared0 F Fr G at_ one R coll set 0 x₀ pc b (held_of Fr pc b hpc) (dec_cleared0 one D told set N x₀ x₁ hl b h) hbase hcoll hG.readsD

/-- Border 8 → 9, at the frozen chain's own block number 8, held. -/
theorem at_laid1 (hl : lookupsOf one = [x₀, x₁]) (b : Block FirstState Claim) (h : (firstChain one D told set N).blocksInOrder[8]? = some b)
    (pc : Piece C Fr (Xi × FirstState) Claim W) (hpc : pc.b = held b) (hbase : ∀ j ∈ pinned (open₁ 2 8), (at_ j).1 < pc.base) (hcoll : CollCell coll) :
    pc.ior.red.Keeps (on₁ F Fr G at_ one R coll 8) (on₁ F Fr G at_ one R coll 9) (L₁ F Fr G at_ one R 8) (L₁ F Fr G at_ one R 9) pc.err :=
  keeps_laid1 F Fr G at_ one R coll set 1 x₁ pc b (held_of Fr pc b hpc) (dec_laid1 one D told set N x₀ x₁ hl b h) hbase hcoll

/-- Border 12 → 13, at the frozen chain's own block number 12, held. -/
theorem at_behind1 (hl : lookupsOf one = [x₀, x₁]) (b : Block FirstState Claim) (h : (firstChain one D told set N).blocksInOrder[12]? = some b)
    (pc : Piece C Fr (Xi × FirstState) Claim W) (hpc : pc.b = held b) (hbase : ∀ j ∈ pinned (open₁ 2 12), (at_ j).1 < pc.base) (hcoll : CollCell coll) :
    pc.ior.red.Keeps (on₁ F Fr G at_ one R coll 12) (on₁ F Fr G at_ one R coll 13) (L₁ F Fr G at_ one R 12) (L₁ F Fr G at_ one R 13) pc.err :=
  keeps_behind1 F Fr G at_ one R coll set 1 x₁ pc b (held_of Fr pc b hpc) (dec_behind1 one D told set N x₀ x₁ hl b h) hbase hcoll

/-- Border 13 → 14, at the frozen chain's own block number 13, held. -/
theorem at_cleared1 (hl : lookupsOf one = [x₀, x₁]) (b : Block FirstState Claim) (h : (firstChain one D told set N).blocksInOrder[13]? = some b)
    (pc : Piece C Fr (Xi × FirstState) Claim W) (hpc : pc.b = held b) (hbase : ∀ j ∈ pinned (open₁ 2 13), (at_ j).1 < pc.base) (hcoll : CollCell coll) (hG : ReadsL G) :
    pc.ior.red.Keeps (on₁ F Fr G at_ one R coll 13) (on₁ F Fr G at_ one R coll 14) (L₁ F Fr G at_ one R 13) (L₁ F Fr G at_ one R 14) pc.err :=
  keeps_cleared1 F Fr G at_ one R coll set 1 x₁ pc b (held_of Fr pc b hpc) (dec_cleared1 one D told set N x₀ x₁ hl b h) hbase hcoll hG.readsD

/-- Border 3 → 4, at the frozen chain's own block number 3, held. -/
theorem at_caller0 (hl : lookupsOf one = [x₀, x₁]) (b : Block FirstState Claim) (h : (firstChain one D told set N).blocksInOrder[3]? = some b)
    (pc : Piece C Fr (Xi × FirstState) Claim W) (hpc : pc.b = held b) (hbase : ∀ j ∈ pinned (open₁ 2 3), (at_ j).1 < pc.base) (hcoll : CollCell coll) (hG : ReadsL G) :
    pc.ior.red.Keeps (on₁ F Fr G at_ one R coll 3) (on₁ F Fr G at_ one R coll 4) (L₁ F Fr G at_ one R 3) (L₁ F Fr G at_ one R 4) pc.err :=
  keeps_caller0 F Fr G at_ one R coll pc b (held_of Fr pc b hpc) (yes_caller0 one D told set N x₀ x₁ hl b h) hbase hcoll hG

/-- Border 9 → 10, at the frozen chain's own block number 9, held. -/
theorem at_caller1 (hl : lookupsOf one = [x₀, x₁]) (b : Block FirstState Claim) (h : (firstChain one D told set N).blocksInOrder[9]? = some b)
    (pc : Piece C Fr (Xi × FirstState) Claim W) (hpc : pc.b = held b) (hbase : ∀ j ∈ pinned (open₁ 2 9), (at_ j).1 < pc.base) (hcoll : CollCell coll) (hG : ReadsL G) :
    pc.ior.red.Keeps (on₁ F Fr G at_ one R coll 9) (on₁ F Fr G at_ one R coll 10) (L₁ F Fr G at_ one R 9) (L₁ F Fr G at_ one R 10) pc.err :=
  keeps_caller1 F Fr G at_ one R coll pc b (held_of Fr pc b hpc) (yes_caller1 one D told set N x₀ x₁ hl b h) hbase hcoll hG

/-- Border 14 → 15, at the frozen chain's own block number 14, held. -/
theorem at_rngRows (hl : lookupsOf one = [x₀, x₁]) (b : Block FirstState Claim) (h : (firstChain one D told set N).blocksInOrder[14]? = some b)
    (pc : Piece C Fr (Xi × FirstState) Claim W) (hpc : pc.b = held b) (hbase : ∀ j ∈ pinned (open₁ 2 14), (at_ j).1 < pc.base) (hcoll : CollCell coll) (hG : ReadsL G) :
    pc.ior.red.Keeps (on₁ F Fr G at_ one R coll 14) (on₁ F Fr G at_ one R coll 15) (L₁ F Fr G at_ one R 14) (L₁ F Fr G at_ one R 15) pc.err :=
  keeps_rngRows F Fr G at_ one R coll pc b (held_of Fr pc b hpc) (yes_rngRows one D told set N x₀ x₁ hl b h) hbase hcoll hG.readsO

/-- Border 18 → 19, at the frozen chain's own last block, held. -/
theorem at_seal (hl : lookupsOf one = [x₀, x₁]) (bw : Block FirstState Claim)
    (hw : sendW one pieces (rootsBefore D (batchRound D)) (groupsTold told (rootsBefore D (lastSendRound D)) (rootsAt D (lastSendRound D))) = some bw)
    (b : Block FirstState Claim) (h : (firstChain one D told set N).blocksInOrder[18]? = some b)
    (pc : Piece C Fr (Xi × FirstState) Claim W) (hpc : pc.b = held b) (hbase : ∀ j ∈ pinned (open₁ 2 18), (at_ j).1 < pc.base) (hcoll : CollCell coll) :
    pc.ior.red.Keeps (on₁ F Fr G at_ one R coll 18) (on₁ F Fr G at_ one R coll 19) (L₁ F Fr G at_ one R 18) (L₁ F Fr G at_ one R 19) pc.err := by
  obtain ⟨asks, ha⟩ := dec_seal one D told set N x₀ x₁ hl bw hw b h
  exact keeps_seal F Fr G at_ one R coll pc b (held_of Fr pc b hpc) asks ha hbase hcoll


/-- **THE PROMISE AT THE FIRST CHAIN's LAST BORDER GIVES THE FILE's LAST TEST's PART ON THAT CHAIN's LAST STATE**. -/
theorem fin_of_on (x : (Xi × FirstState) × Fr.E.Str) (h : on₁ F Fr G at_ one R coll 19 x) : firstEndOk one x.1.2 = true := by
  have hs : shape₁ (plan₁ one) (readers₁ one) (book₁ one) (n₁ one) (slots₁ one) 19 x.1.2 = true := h.elim (fun hn => absurd rfl hn) (·.1)
  rw [on₁_two F Fr G at_ one R coll 19 x h] at hs
  exact finD_of_shape one x.1.2 hs

end

end Johnson.RunOne.KeyRows1

#print axioms Johnson.RunOne.KeyRows1.at_laid0
#print axioms Johnson.RunOne.KeyRows1.at_behind0
#print axioms Johnson.RunOne.KeyRows1.at_cleared0
#print axioms Johnson.RunOne.KeyRows1.at_laid1
#print axioms Johnson.RunOne.KeyRows1.at_behind1
#print axioms Johnson.RunOne.KeyRows1.at_cleared1
#print axioms Johnson.RunOne.KeyRows1.at_seal
#print axioms Johnson.RunOne.KeyRows1.flat_length
#print axioms Johnson.RunOne.KeyRows1.finD_of_shape
#print axioms Johnson.RunOne.KeyRows1.fin_of_on
#print axioms Johnson.RunOne.KeyRows1.at_caller0
#print axioms Johnson.RunOne.KeyRows1.at_caller1
#print axioms Johnson.RunOne.KeyRows1.at_rngRows
