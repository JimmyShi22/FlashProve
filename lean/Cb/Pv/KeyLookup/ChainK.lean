-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Pv/KeyLookup/ChainK.lean: links and chains that carry knowledge soundness alone. It imports the
library alone.

Why. The library's `Link` (Ior/KnowCollRulesChain.lean) holds a reduction, an honest side H, an
extractor and a record of numbers. The lookup with parts is laid, at first, with Know alone: it has
no honest side and no numbers but its errors to give. So beside Link and Chain stand thin twins
without H.
  `LinkK K A B`     a reduction from joint A to joint B, an extractor, the errors. `LinkK.ofLink`
                   forgets H and keeps of the numbers the errors.
  `LinkK.Know`, `.Carry`, `.Ok`   Know between the joints' relaxed relations; the joints' condition
                   «on» is handed on; both.
  `LinkK.seq`, `ofLink_seq` (by rfl), `seq_ok`   two in a row; forgetting commutes with it; Ok goes
                   through, by the library's own know_seq.
  `ChainK` with `one`, `snoc`, `link`, `append`, `fam`, `AllK`, `ofChain`   the library's Chain, of
                   LinkK.
  `chainK_ok`       if every link is Ok, the chain read as one link is Ok.
Under: nothing beyond the binders. Does not say: anything on acceptance, an honest run, or the
numbers pBad, pHid, bud, cov. A departure from `Link`: the third field is e : Err R.shape, not the
library's Nums. After: Joint, Link, Chain, know_seq, IOR.extSeq, IOR.red_seq_out are the library's;
chainK_ok is cut from its chain_goodB (Ior/KnowCollRulesChain.lean), seq_ok's second half from
goodB_seq_ext (Ior/Masked.lean); the cut «Know's half without an honest side» is after
Cb/Pv/Lookup/Know/KnowAt.lean; the defining equations and ofChain_link, allK_append, allK_fam follow
the library's pattern for Chain.

-/
import Ior.KnowCollRulesChain   -- Joint, Link, Chain
import Ior.SeqProofs            -- know_seq, IOR.extSeq, IOR.red_seq_out

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Lk6
open Iop Prob IOR

/-- A link without its honest side: the library's Link (Ior/KnowCollRulesChain.lean) less H; of P
the errors. -/
structure LinkK (K : Type) (A B : Joint K) : Type 1 where
  R   : IOR A.X A.E B.X B.E
  ext : A.X × A.E.Str → Tr R.shape → B.W → A.W
  e   : Err R.shape

namespace LinkK
variable {K : Type} {A B C : Joint K}
/-- forget H -/
def ofLink (l : Link K A B) : LinkK K A B := ⟨l.R, l.ext, l.P.err⟩
def Know (l : LinkK K A B) : Prop := l.R.red.Know A.rels.on A.rels.relR B.rels.relR l.ext l.e
def Carry (l : LinkK K A B) : Prop := ∀ a τ b, A.rels.on a → l.R.red.out a τ = some b → B.rels.on b
def Ok (l : LinkK K A B) : Prop := l.Know ∧ l.Carry
noncomputable def seq (l : LinkK K A B) (l' : LinkK K B C) (d : A.W) : LinkK K A C where
  R := l.R.seq l'.R
  ext := IOR.extSeq l.R l'.R l.ext l'.ext d
  e := Err.app l.e l'.e
theorem ofLink_seq (l : Link K A B) (l' : Link K B C) (d : A.W) :
    ofLink (l.seq l' d) = (ofLink l).seq (ofLink l') d := rfl
theorem ok_of_goodB {l : Link K A B} (g : l.GoodB) : (ofLink l).Ok := ⟨g.know, g.onOut⟩
/-- the rule for two: know_seq OWN; the carry: goodB_seq_ext's lines (Ior/Masked.lean) -/
theorem seq_ok {l : LinkK K A B} {l' : LinkK K B C} (d : A.W) (h : l.Ok) (h' : l'.Ok) :
    (l.seq l' d).Ok :=
  ⟨know_seq _ _ _ _ _ _ l.R l'.R _ _ _ _ _ _ _ _ l.ext l'.ext l.e l'.e d h.1 h'.1 h.2,
    fun a τ c ha hc => by
      obtain ⟨b, hb, hc'⟩ :=
        Option.bind_eq_some_iff.1 ((IOR.red_seq_out l.R l'.R a τ).symm.trans hc)
      exact h'.2 b _ c (h.2 a _ b ha hb) hc'⟩
end LinkK

/-- The library's Chain, of LinkK. -/
inductive ChainK (K : Type) : Joint K → Joint K → Type 1
  | one {A B : Joint K} (l : LinkK K A B) : ChainK K A B
  | snoc {A B C : Joint K} (c : ChainK K A B) (l : LinkK K B C) : ChainK K A C

namespace ChainK
variable {K : Type}
noncomputable def link : {A B : Joint K} → ChainK K A B → A.W → LinkK K A B
  | _, _, .one l, _ => l
  | _, _, .snoc c l, d => (c.link d).seq l d
def append : {A B C : Joint K} → ChainK K A B → ChainK K B C → ChainK K A C
  | _, _, _, c, .one l => .snoc c l
  | _, _, _, c, .snoc c' l => .snoc (c.append c') l
def fam (J : ℕ → Joint K) (b : ∀ l, LinkK K (J l) (J (l + 1))) :
    (n : ℕ) → ChainK K (J 0) (J (n + 1))
  | 0 => .one (b 0)
  | n + 1 => .snoc (fam J b n) (b (n + 1))
def AllK : {A B : Joint K} → ChainK K A B → Prop
  | _, _, .one l => l.Ok
  | _, _, .snoc c l => c.AllK ∧ l.Ok
/-- forget H, link by link -/
def ofChain : {A B : Joint K} → Chain K A B → ChainK K A B
  | _, _, .one l => .one (.ofLink l)
  | _, _, .snoc c l => .snoc (ofChain c) (.ofLink l)

/-! the defining equations, as the library has them for Chain (Ior/KnowCollRulesChain.lean) -/
theorem link_one {A B : Joint K} (l : LinkK K A B) (d : A.W) : (ChainK.one l).link d = l := by
  rw [link]
theorem link_snoc {A B C : Joint K} (c : ChainK K A B) (l : LinkK K B C) (d : A.W) :
    (c.snoc l).link d = (c.link d).seq l d := by rw [link]
theorem append_one {A B C : Joint K} (c : ChainK K A B) (l : LinkK K B C) :
    c.append (.one l) = c.snoc l := by rw [append]
theorem append_snoc {A B C D : Joint K} (c : ChainK K A B) (c' : ChainK K B C) (l : LinkK K C D) :
    c.append (c'.snoc l) = (c.append c').snoc l := by rw [append]
theorem allK_one {A B : Joint K} (l : LinkK K A B) : (ChainK.one l).AllK ↔ l.Ok := by rw [AllK]
theorem allK_snoc {A B C : Joint K} (c : ChainK K A B) (l : LinkK K B C) :
    (c.snoc l).AllK ↔ c.AllK ∧ l.Ok := by rw [AllK]
theorem ofChain_one {A B : Joint K} (l : Link K A B) : ofChain (.one l) = .one (.ofLink l) := by
  rw [ofChain]
theorem ofChain_snoc {A B C : Joint K} (c : Chain K A B) (l : Link K B C) :
    ofChain (c.snoc l) = (ofChain c).snoc (.ofLink l) := by rw [ofChain]

/-- forgetting H commutes with reading a chain as one link -/
theorem ofChain_link : {A B : Joint K} → (c : Chain K A B) → (d : A.W) →
    LinkK.ofLink (c.link d) = (ofChain c).link d
  | _, _, .one l, d => by rw [Chain.link_one, ofChain_one, link_one]
  | _, _, .snoc c l, d => by
      rw [Chain.link_snoc, LinkK.ofLink_seq, ofChain_snoc, link_snoc, ofChain_link c d]
theorem allK_append : {A B C : Joint K} → (c : ChainK K A B) → (c' : ChainK K B C) →
    ((c.append c').AllK ↔ c.AllK ∧ c'.AllK)
  | _, _, _, c, .one l => by rw [append_one, allK_snoc, allK_one]
  | _, _, _, c, .snoc c' l => by
      rw [append_snoc, allK_snoc, allK_snoc, allK_append c c']
      exact and_assoc
theorem allK_fam (J : ℕ → Joint K) (b : ∀ l, LinkK K (J l) (J (l + 1))) :
    (n : ℕ) → (∀ l, l ≤ n → (b l).Ok) → (fam J b n).AllK
  | 0, h => by
      rw [fam, allK_one]
      exact h 0 (Nat.le_refl 0)
  | n + 1, h => by
      rw [fam, allK_snoc]
      exact ⟨allK_fam J b n fun l hl => h l (Nat.le_succ_of_le hl), h (n + 1) (Nat.le_refl _)⟩
end ChainK

/-- If every link is Ok, the chain read as one link is Ok. Cut from chain_goodB
(Ior/KnowCollRulesChain.lean). -/
theorem chainK_ok {K : Type} {A B : Joint K} (c : ChainK K A B) (d : A.W) :
    c.AllK → (c.link d).Ok := by
  induction c with
  | one l => intro h; rw [ChainK.link]; rw [ChainK.AllK] at h; exact h
  | snoc c l ih =>
    intro h; rw [ChainK.AllK] at h; rw [ChainK.link]; exact LinkK.seq_ok d (ih h.1) h.2

end Lk6

#print axioms Lk6.LinkK.ofLink_seq
#print axioms Lk6.LinkK.ok_of_goodB
#print axioms Lk6.LinkK.seq_ok
#print axioms Lk6.ChainK.ofChain_link
#print axioms Lk6.ChainK.allK_append
#print axioms Lk6.ChainK.allK_fam
#print axioms Lk6.chainK_ok
