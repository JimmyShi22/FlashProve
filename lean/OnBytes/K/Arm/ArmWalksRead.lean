-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/K/Arm/ArmWalksRead.lean: what the lax verifier's clause on the walks asks at an entry's
typed string, at the family that the encoding `implArmD` reads out of one oracle, from one yes of
the strict reader.

`walks_armD` (OnBytes/TypedOracleCompiler/Slice/ArmWalksAt.lean) leaves as hypotheses what does not look at the
family: what the format's reader said of each opening, forms, roots, widths, lengths and bounds.
OnBytes/K/Left/ has each of them from the strict reader's equation, at any hash: LaxReadAs.lean,
LaxLens.lean, LaxShape.lean, LaxForms.lean, LaxPagesOwn.lean, Asm.lean. Here they are put in. For
proofs only; the program does not import this file.

Main name.
 `walks_armD_read`: `Walks D (famG (pageArmD …) g) embS embE2 (r0 :: r1 :: more) o` (the two roots
   as digests), for every oracle g on bit strings, every number K of blocks and every list `more`
   behind the two roots.

What is asked.
 Of the file: `Fmt.readChainX (hOfG g) (specOf D st) seen b i = some (o, j)`: the strict reader's
   yes at the hash made of the same oracle g, under D's description with a statement st.
 Of the description: the sibling's limits `PQ.ok D.base`; all stored tables have the depth `D.a`
   and the plan's length of salts (`hsame`: `stored_same` has it from `D.ok`); the statement's items
   hold the two roots (`hit`).
 Of the encoding and the bodies over the second interface, which are choices of whoever writes
   them: the code of leaves is made for the plan's length of salts (`hn`); the chain's own symbols
   are written by one way e2, lifted (`hemb`); the map of leaf queries reads `e2 s x sym` as the
   format's spelling of that leaf and `embE2 y` as the line's body of the stored symbol y, and keeps
   the salt (`hselO`, `hselS`).

What is not claimed. That any encoding, bodies or map meet what is asked of them. Nothing on the
chain's queries. Nothing on soundness.


-/
import OnBytes.TypedOracleCompiler.Slice.ArmWalksAt
import OnBytes.K.Left.LaxForms
import OnBytes.K.Left.LaxShape
import OnBytes.K.Left.LaxPagesOwn

set_option autoImplicit false

noncomputable section

namespace OnBytes.K.Arm
open OnBytes.K.Left
open Rom _root_.Compile TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Iop TypedOracleCompiler.Run TypedOracleCompiler.Slice
open TypedOracleCompiler.Run.Apart TypedOracleCompiler.Run.PageG TypedOracleCompiler.Run.SeedPage
open TypedOracleCompiler.Run.SeedPoints TypedOracleCompiler.Run.LinkAlong TypedOracleCompiler.Run.LinkOf
open TypedOracleCompiler.Run.ArmDirect TypedOracleCompiler.Run.RowsG TypedOracleCompiler.Strings
open TypedOracleCompiler.Slice.ArmWalks
open TypedOracleCompiler.Run.PQ (XD SOf)
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run
open _root_.Run.PQ (SgX)

variable {I0 X0 I2 X2 : Type} (L0 : _root_.Iop.BatchProtocol I0 X0) (L2 : BatchProtocolWithLeafBody I2 X2) (D : XD)
  (p0 p1 : PlainPart (shapeOf L2 .test) (annOf L2 .test))
  (isP0 isP1 : PlainPart (shapeOf L2 .test) (annOf L2 .test) → Bool) (cfgL : List (Dig 256)) (sh : Bits)
  (hp0 : ∀ p, isP0 p = true ↔ p = p0) (hp1 : ∀ p, isP1 p = true ↔ p = p1) (rest : ByteArray)
  (l : ℕ) (hlt : l < 2 ^ 48) (hne : l ≠ _root_.Fmt.recordLabel)
  (f0 : PCode (FbIn 256 L2 .link)) (h0 : ∀ q s, f0.put q = some s → Is160 l s)
  (K : ℕ) (F : FbPair (strung L0) L2) (pR : PCode (FbIn 256 (strung L0) .link × Fin (K + 1)))
  (hR : ∀ x s, pR.put x = some s → Is162 l s) (G : LeafPair (strung L0) L2) (nb : ℕ)
  (hcfg : D.base.cfg.size = 32) (back : StrCode (AllPts 256 K L2)) (g : Fam (rom 256))

/-- The clause on the walks at `implArmD`'s family, from one yes of the strict reader. -/
theorem walks_armD_read (hok : TypedOracleCompiler.Run.PQ.ok D.base = true)
    (hsame : ∀ t ∈ D.stored.flatten, t.sh.a = D.a ∧ t.salt = D.base.plan.salt)
    (hn : nb = 8 * D.base.plan.salt) {st : ByteArray} {seen : _root_.Fmt.Seen} {b : ByteArray}
    {i : ℕ} {o : _root_.Fmt.ChainOut} {j : ℕ}
    (e : _root_.Fmt.readChainX (m := Id) (hOfG g) (specOf D st) seen b i = some (o, j))
    (r0 r1 : ByteArray)
    (hit : ∀ t ∈ D.stored.flatten,
      _root_.Fmt.itemRoot st t.item = some (if t.item == 1 then r1 else r0))
    {embS : (p : OPos (_root_.Run.Twin.up (SOf D.C D.ds))) →
      OSym (_root_.Run.Twin.up (SOf D.C D.ds)) p → Body L2}
    {e2 : Enc1 (Body L2)} (hemb : ∀ q a, embS (.inr q) a = embLS D.C (liftT e2) D.ds q a)
    {embE2 : SgX → Body L2} (c : StrCode (ℕ × List UInt64))
    (hselO : ∀ (s : _root_.Fmt.Shape) (x : Fin (2 ^ s.a)) (sym : Fin s.W → UInt64) (z : Bits),
      G.sel ⟨e2 s x sym, z⟩ =
        some ⟨spell2 164 (_root_.Fmt.leafPlace s.tree s.W (D.base.plan.salt / 8),
          2 ^ s.a + x.val, _root_.Fmt.colBytes (List.ofFn sym) ++
            _root_.Fmt.zeroBytes (_root_.Fmt.fillLen s.W D.base.plan.salt)), z⟩)
    (hselS : ∀ (y : SgX) (z : Bits),
      G.sel ⟨embE2 y, z⟩ = some ⟨embX D.a D.base.plan.salt c y, z⟩)
    (more : List (Dig 256)) :
    Walks D (famG (pageArmD L2 p0 p1 isP0 isP1 cfgL sh hp0 hp1 rest K l hlt hne f0 h0 F pR
      hR G (KeyLeaves.leavesAt L0 nb D.base.cfg) D.base.cfg hcfg back) g) embS embE2
      (bytesToDig r0 :: bytesToDig r1 :: more) o := by
  have hown : ∀ r ∈ (specOf D st).base.rounds, ∀ x ∈ r.opens, ∃ n, x.2 = .own n :=
    opens_own (S₀ := D.base) hok
  have hz : ∀ n t i s b, ByteArray.size (hOfG g n t i s b) = _root_.Fmt.dlen n :=
    fun n t i s b => _root_.Run.PQ.size_HO (oB (g ())) (size_oB g) n t i s b
  have hrand : (specOf D st).base.rand ≠ .none := by
    intro hr
    have hr' : D.base.rand = .none := hr
    simp only [TypedOracleCompiler.Run.PQ.ok, Bool.and_eq_true] at hok
    have h2 := hok.2
    rw [hr'] at h2
    cases h2
  have h32 : ∀ run, o.run = some run → run.size = 32 := by
    intro run hrun
    obtain ⟨run', h1, h2⟩ := run_of_read hz e hrand
    obtain rfl : run' = run := Option.some.inj (h1.symm.trans hrun)
    exact h2
  refine Walks.longer (walks_armD L0 L2 D p0 p1 isP0 isP1 cfgL sh hp0 hp1 rest l hlt hne f0 h0 K F
    pR hR G nb hcfg back g hz hemb (forms_on D) (rts_on D hok e) D.base.plan.salt hn c
    (salt_small (base_ok hok))
    (fun run hrun op hop => by
      obtain ⟨-, -, -, -, -, R⟩ := readAs_own e hown hrun op hop
      exact R)
    (own_form D hok e) (own_root D hok e) (fun op hop => (lens_own e op hop).2) h32
    (fun op hop => by
      obtain ⟨d, hd, ht⟩ := own_tree D hok e op hop
      exact own_bounds D hok d hd op.sh ht)
    hselO
    (fun op hop => by
      obtain ⟨-, -, -, R⟩ := readAs_sto e hown op hop
      exact R)
    (fun op hop => (lens_sto_at e hown hsame rfl op hop).1)
    (sto_root D hok e r0 r1 hit)
    (fun op hop => (lens_sto_at e hown hsame rfl op hop).2.1)
    (fun op hop => (lens_sto_at e hown hsame rfl op hop).2.2)
    (fun op hop => by
      obtain ⟨-, h2, -, h4, h5⟩ := sto_facts e hown hsame rfl op hop
      exact ⟨h2, h4, h5⟩)
    hselS) more

end OnBytes.K.Arm
