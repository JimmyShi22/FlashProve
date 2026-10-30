-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Slice/EntryVerdictShortEq.lean: `verifyEL` (OnBytes/TypedOracleCompiler/Slice/EntryVerdictShort.lean) is
`verifyE`: the equation, in both directions.

Why. `verifyEL_yes` carries a yes alone. `verifyEL` tests its short list at run time; here the list
`lstX` is shown to pass both tests always, so no refusal comes from the list, and the two functions
have one value on all arguments.

  `verifyLXL_eq` (namespace TypedOracleCompiler.Run.Thin): where the list always increases strictly and
    always holds every read position, `verifyLXL` is `verifyLX`, under `verifyLXL_yes`'s premises.
  `insU_sub`, `insU_mem_iff`, `insU_sorted`, `sortU_sorted`, `sortU_mem`: `sortU key l` increases
    strictly under the key; for a key that is one to one it has the members of l.
  `lstX_sorted`, `lstX_cover`: the two tests at `lstX`.
  `laxEL_eq`: `laxEL` is `laxE`.
  `yesShort_eq`: at two roots, `cmpEL` and `laxEL` together say what `whyOutE`'s "YES" says.
  `verifyEL_eq`: `verifyEL G hok x a = verifyE G hok x a`.
What is claimed is an equation between two functions, and no more. Not claimed: that either says yes
on any value; any time or memory. A compiled program's answer is no proof in Lean of either side's
value. The limits named in the head of OnBytes/TypedOracleCompiler/Slice/EntryVerdict.lean hold here too.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.TypedOracleCompiler.Slice.EntryVerdictShort

set_option autoImplicit false

namespace TypedOracleCompiler.Run.Thin
open TypedOracleCompiler.Iop Rom _root_.Compile TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Run.Twin
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run _root_.Run.Thin

variable {I X : Type} {lam K : ℕ} (Lf : Unit → BatchProtocolWithLeafBody I X) (g : Fam (typedOracleFamily lam K (Lf ())))
  {Y : Type} {E : ExtSpec} {M : Type} (mk : Finset E.Pos → M) (tst : M → E.Pos → Bool)
  {M' : Type} (mk' : Finset E.Pos → M') (tst' : M' → E.Pos → Bool) [DecidableEq E.Pos]

/-- Where the list passes both run-time tests at all arguments, `verifyLXL` is `verifyLX`, under the
premises on the wire, the key and the two tests of membership that stand in the statement. -/
theorem verifyLXL_eq (early : X → X) (late : Option ℕ) (t : Tag) (P : PS Y E)
    (wq : ProtocolQueryLayout lam K P.up) (wqOf : List E.Pos → ProtocolQueryLayout lam K P.up)
    (hall' : ∀ L, (wqOf L).ext.all = L) (hsh : ∀ L, (wqOf L).sh = wq.sh)
    (hl : ∀ L, (wqOf L).ext.leaf = wq.ext.leaf) (hw : ∀ L, (wqOf L).ext.which = wq.ext.which)
    (hd : ∀ L, (wqOf L).ext.depth = wq.ext.depth) (hb : ∀ L, (wqOf L).ext.build = wq.ext.build)
    (hn : ∀ L, (wqOf L).nOpen = wq.nOpen) (hm : ∀ L, (wqOf L).maxDepth = wq.maxDepth)
    (key : E.Pos → ℕ) (s : wq.ext.all.Pairwise (fun a b => key a < key b))
    (hall : ∀ p, p ∈ wq.ext.all) (htst : ∀ R p, tst (mk R) p = true ↔ p ∈ R)
    (htst' : ∀ R p, tst' (mk' R) p = true ↔ p ∈ R)
    (lst : Y → Rho (up P.S) → List E.Pos)
    (hs : ∀ x ρ, (lst x ρ).Pairwise (fun a b => key a < key b))
    (hc : ∀ x ρ, ∀ p ∈ P.extReads x ρ, p ∈ lst x ρ)
    (embS : (p : OPos (up P.S)) → OSym (up P.S) p → Body (Lf ()))
    (embP : PlainPart (up P.S) P.ann → PlainPart (shapeOf (Lf ()) t) (annOf (Lf ()) t))
    (xin : Y → Option X) (embE : E.Sym → Body (Lf ())) (depthReq : ℕ) (cms : List (Dig lam))
    (x : Y) (π : OneProtocolProof lam P.up) :
    verifyLXL Lf g mk' tst' early late t P wq.sh wqOf key lst embS embP xin embE depthReq cms x π =
      verifyLX Lf g mk tst early late t P wq embS embP xin embE depthReq cms x π := by
  unfold verifyLXL verifyLX
  cases chainP Lf g early late t cms (xin x) π.salt π.rtreq P.S P.ann wq.sh embP 0
      .first π.roots π.plains with
  | none => rfl
  | some r =>
    obtain ⟨ρ, rts, ph⟩ := r
    show (decide ((lst x ρ).Pairwise (fun a b => key a < key b)) &&
      decide (∀ p ∈ P.extReads x ρ, p ∈ lst x ρ) &&
      afterLX Lf g mk' tst' P (wqOf (lst x ρ)) embS embE depthReq cms x π ρ rts ph) =
      afterLX Lf g mk tst P wq embS embE depthReq cms x π ρ rts ph
    rw [decide_eq_true (hs x ρ), decide_eq_true (hc x ρ), Bool.and_self, Bool.true_and]
    exact afterLX_listed Lf g mk tst mk' tst' P wq (wqOf (lst x ρ)) (hsh _) (hl _) (hw _) (hd _)
      (hb _) (hn _) (hm _) key s hall htst htst' embS embE depthReq cms x π ρ rts ph
      (by rw [hall']; exact hs x ρ) (fun p hp => by rw [hall']; exact hc x ρ p ((htst _ p).1 hp))

end TypedOracleCompiler.Run.Thin

namespace TypedOracleCompiler.Slice
open Rom Prob _root_.Compile TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Iop TypedOracleCompiler.Run
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open TypedOracleCompiler.Run.PQ (XD BodyD OwnE SOf bodyS wX)
open _root_.Run.PQ (View SgX weX)
open TypedOracleCompiler.Run.Thin (verifyLX verifyLXL verifyLXL_eq)
open OnBytes.Tie (EntryGround linkAtCfg keyAt AskedE)
open OnBytes.Slice (GE NZ seedEntry seedOfDrawnC)

/-- A member of `insU key x l` is x or a member of l. -/
theorem insU_sub {α : Type} (key : α → ℕ) (x y : α) :
    ∀ l : List α, y ∈ insU key x l → y = x ∨ y ∈ l
  | [], h => Or.inl (List.mem_singleton.1 h)
  | z :: l, h => by
      unfold insU at h
      split at h
      · exact List.mem_cons.1 h
      · split at h
        · exact Or.inr h
        · rcases List.mem_cons.1 h with e | m
          · exact Or.inr (e ▸ List.mem_cons_self)
          · rcases insU_sub key x y l m with e | m'
            · exact Or.inl e
            · exact Or.inr (List.mem_cons_of_mem _ m')

/-- For a key that is one to one: the members of `insU key x l` are x and the members of l. -/
theorem insU_mem_iff {α : Type} (key : α → ℕ) (hk : Function.Injective key) (x y : α) :
    ∀ l : List α, y ∈ insU key x l ↔ y = x ∨ y ∈ l
  | [] => by simp [insU]
  | z :: l => by
      refine ⟨insU_sub key x y (z :: l), fun h => ?_⟩
      unfold insU
      split
      · exact List.mem_cons.2 h
      · split
        · rename_i _ e
          rcases h with rfl | m
          · exact hk e ▸ List.mem_cons_self
          · exact m
        · rcases h with e | m
          · exact List.mem_cons_of_mem _ ((insU_mem_iff key hk x y l).2 (Or.inl e))
          · rcases List.mem_cons.1 m with e | m'
            · exact e ▸ List.mem_cons_self
            · exact List.mem_cons_of_mem _ ((insU_mem_iff key hk x y l).2 (Or.inr m'))

/-- `insU` keeps a list increasing strictly under the key. -/
theorem insU_sorted {α : Type} (key : α → ℕ) (x : α) :
    ∀ l : List α, l.Pairwise (fun a b => key a < key b) →
      (insU key x l).Pairwise (fun a b => key a < key b)
  | [], _ => List.pairwise_singleton _ _
  | z :: l, h => by
      obtain ⟨hz, hl⟩ := List.pairwise_cons.1 h
      unfold insU
      split
      · rename_i h1
        refine List.pairwise_cons.2 ⟨fun y hy => ?_, h⟩
        rcases List.mem_cons.1 hy with rfl | m
        · exact h1
        · exact lt_trans h1 (hz y m)
      · split
        · exact h
        · rename_i h1 h2
          refine List.pairwise_cons.2 ⟨fun y hy => ?_, insU_sorted key x l hl⟩
          rcases insU_sub key x y l hy with rfl | m
          · omega
          · exact hz y m

/-- `sortU key l` increases strictly under the key. -/
theorem sortU_sorted {α : Type} (key : α → ℕ) :
    ∀ l : List α, (sortU key l).Pairwise (fun a b => key a < key b)
  | [] => List.Pairwise.nil
  | x :: l => insU_sorted key x (sortU key l) (sortU_sorted key l)

/-- For a key that is one to one: `sortU key l` has the members of l. -/
theorem sortU_mem {α : Type} (key : α → ℕ) (hk : Function.Injective key) (y : α) :
    ∀ l : List α, y ∈ sortU key l ↔ y ∈ l
  | [] => Iff.rfl
  | x :: l => by
      show y ∈ insU key x (sortU key l) ↔ y ∈ x :: l
      rw [insU_mem_iff key hk, sortU_mem key hk y l, List.mem_cons]

section
variable {X : Type} (D : XD) (dec : X → View → Bool) {Bd : Type} (B : BodyD Bd) (E : OwnE Bd D)
    (early : X → X)
  (Tf : Unit → InteractiveOracleProof Unit (oneExternalString (2 ^ D.a) SgX))

/-- `lstX` increases strictly under `ix2`. -/
theorem lstX_sorted (x : X) (ρ : Rho (_root_.Run.Twin.up (PSXE D dec).S)) :
    (lstX D dec x ρ).Pairwise (fun p q => ix2 (2 ^ D.a) p < ix2 (2 ^ D.a) q) :=
  sortU_sorted _ _

/-- `lstX` holds every external position that the link reads. -/
theorem lstX_cover (x : X) (ρ : Rho (_root_.Run.Twin.up (PSXE D dec).S))
    (p : Fin (2 ^ D.a) ⊕ Fin (2 ^ D.a)) (hp : p ∈ (PSXE D dec).extReads x ρ) :
    p ∈ lstX D dec x ρ :=
  (sortU_mem _ (ix2_inj _) p _).2 (List.mem_toFinset.1 hp)

/-- `laxEL` is `laxE`. -/
theorem laxEL_eq
    (F : Fam (TypedOracleCompiler.Compile.Batch.typedOracleFamily 256 (D.K + 1) (LXE (Bd := Bd) D early (Tf ()))))
    (cms : List (Dig 256)) (x : X) (π : OneProtocolProof 256 (PSXE D dec).up) :
    laxEL D dec B E early Tf F cms x π = laxE D dec B E early Tf F cms x π :=
  verifyLXL_eq (fun _ => LXE (Bd := Bd) D early (Tf ())) F (mkX D.a) (tstX D.a) id
    (memX D.a) early none .link
    (PSXE D dec) (wqXE D dec) (wqXL D dec) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
    (fun _ => rfl)
    (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (ix2 (2 ^ D.a)) (weX_sorted D.a)
    (weX_all D.a) (tstX_eq D.a) (memX_eq D.a) (lstX D dec) (lstX_sorted D dec) (lstX_cover D dec)
    E.emb (embPXE D early (Tf ())) some B.embE 0 cms x π

end

section
variable {lg s : ℕ} (D : XD) (hok : TypedOracleCompiler.Run.PQ.ok D.base = true) (d₁ : Sd1 lg s)
  (dec : XE AnsT lg s → _root_.Run.PQ.View → Bool)
  (F : Fam (typedOracleFamily 256 (D.K + 1)
    (LXE (Bd := List Bool) D (earlyTwo (A := AnsT × AnsT) d₁) (TSE D (seedEntry lg s)))))

/-- At two roots, `cmpEL` and `laxEL` together say what `whyOutE`'s "YES" says. -/
theorem yesShort_eq (cms : List (Dig 256)) (h2 : cms.length = 2) (x : XE AnsT lg s)
    (π : OneProtocolProof 256 (PSXE D dec).up) :
    (cmpEL D (earlyTwo d₁) (seedEntry lg s) (seedOfDrawnC lg s) F cms 0 x.2 &&
      laxEL D dec (bodyS D.a D.base.plan.salt) (ownES D hok) (earlyTwo d₁)
        (fun _ => TSE D (seedEntry lg s)) F cms x π) =
      (whyOutE D hok d₁ dec F cms x π == "YES") := by
  apply Bool.eq_iff_iff.2
  rw [Bool.and_eq_true, beq_iff_eq, whyOutE_yes, laxEL_eq, cmpEL_eq]
  exact ⟨fun h => ⟨h2, h.1, h.2⟩, fun h => ⟨h.2.1, h.2.2⟩⟩

end

variable (G : EntryGround)
  (hok : ∀ c : ByteArray, c.size = 32 → TypedOracleCompiler.Run.PQ.ok (entryXD G c).base = true)

/-- **`verifyEL` is `verifyE`.** -/
theorem verifyEL_eq (x : EntryStmt) (a : AskedE) : verifyEL G hok x a = verifyE G hok x a := by
  unfold verifyEL verifyE
  cases assembleS (entryXD G x.c)
      (decRun (linkAtCfg G.q x.c) G.q.link.table.v G.q.link.table.cubeBits G.q.link.table.answers)
      a.out with
  | none => rfl
  | some π =>
    simp only []
    rw [yesShort_eq (entryXD G x.c) (hok x.c x.hc) _ _ _
      [_root_.Run.bytesToDig a.first.root, _root_.Run.bytesToDig a.further.root] rfl]

end TypedOracleCompiler.Slice
