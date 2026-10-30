-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Cb/Pv/Att/Link.lean: the link of a sub-proof as a whole, at letters: the lookup, the sub-proof's own
rounds, the sending of the tables' message, the smallness test's draw, the sending of the digits'
message, the digits' lookup with the batching draw: one statement of knowledge soundness, in the
true order.

Definitions, statements and proofs. The frame is that of Cb/Sub/SumOrder.lean: a block has `KnowAt`
(Cb/G6/Cut.lean) at the tuples of the oracle messages that stand when it runs, and at no others; at
a sending the signature grows (`Sig.sum`) and the witness in front is made from the messages sent
and the witness behind. Of the sub-proof's own rounds the statement uses only that they are a chain
c with `c.OK` (Cb/Pv/Att/Chain.lean).

Main names:
  `frame2`: R, the sending of N₁, T₁, the sending of N₂, T₂, in a row: `sum_step` behind
    `sum_order`. `frame2Red`, `frame2Ext`, `frame2Err`: the reduction, the extractor, the errors.
  `Ch.atM π c`: a chain at the tuples M, read at tuples M' through π : M' → M, with `Ch.todo_atM`,
    `Ch.ok_atM`. At M' := M × U the part U is then held fixed while the chain runs: a step of
    book-keeping, not a statement on a message that is sent behind the chain.
  `subR R₁ c cl`: the lookup R₁, the chain c, and a step without rounds that lays the ledger `cl e`
    of the verifier's claims beside the chain's last statement e.
  `look_seam`: a lookup that ends at a joint B₁ of its own ends at the chain's claim, if that claim
    gives B₁.
  `subR_knowAt`: `KnowAt` of `subR`, from the lookup's joint A to `virtJ` (Cb/Sub/LateJoin.lean):
    B₀, and the ledger's pull-back to the early entries holds.
  `sub_link`: THE STATEMENT: `KnowInto` of the whole, from `S₁.over A` to `((S₁.sum N₁).sum N₂).over
    C₂`.
  `dig_batch`: the last block cut in two: a block that ends at a ledger with nothing left open
    beside it, and the draw that batches the ledger into one form (`led_batch`, Cb/Sub/Joint.lean):
    it serves as `hDig`.
  `linkCh units T`, `linkCh_ok`: the chain of an attention sub-proof's own rounds
    (Cb/Pv/Att/Gaps.lean) and its conditions: so `sub_link` at `linkCh units T` is the attention
    link's statement, and there the chain has no premise but the seven equations in the record
    `TailG`.

Premises of `sub_link`, by kind.
  The chain's conditions: `hc`.
  Other blocks' `KnowAt`: `hLook` (the lookup, into the chain's claim at its start), `hRng` (the
    smallness test's draw, from Rl₁ to C₁), `hDig` (the digits' lookup with the batching draw, from
    Rl₂ to C₂).
  The ends: `hEnd`: B₀ and the ledger's pull-back give what the chain owes at its end (`Ch.Last`)
    and what rides (A0).
  The seams: `hs₁`: Rl₁ gives B₀, agreement of the late entries with their forms, and the ledger on
    early and late entries. `hs₂`: Rl₂ gives C₁, with the witness made from the digits' message.
  The two sendings' three premises each (fair seeds, list bounds, evading samples).
  Conditions on statements: `hOn`, `ho₁`, `ho₂`, and `hn`: the ledger has at most n claims. d, d':
    defaults of the composed extractor.

Limits: those of Cb/Sub/SumOrder.lean and Cb/Pv/Att/Chain.lean. Nothing on an honest prover,
completeness or zero knowledge. No block but the chain is given: R₁, T₁, T₂ are letters. The witness
in front of the first sending has the type Wp. At the meant value `bk₁` does not read its first
argument and forgets what T₁'s witness holds more: then no block in front of that sending can say
anything of it. By type `bk₁` may put the late message into Wp: `hLook` would then be a hypothesis
on a late part of the witness in front of draws. `hRng` is a
hypothesis whose joint C₁ reads, through `bk₂`, the digits' message, which is sent behind T₁'s draw.
`KnowAt` binds that part at the transcript's end: so `hRng` asks that few draws are bad although the
digits are picked behind the draw. It can hold only if C₁ says of the digits their ranges as well as
their sums. It is to be proved at a value, not assumed. A claim that is tested at a point which the
lookup draws must come in inside A and not stand in A0, B₀ or Dn. The sending of S₁ and its error
are not in the list. That the ledger `cl e` is the programs' is not said here. `dig_batch` asks that
nothing is left open beside the ledger: a claim that leaves the sub-proof does not pass it.
-/
import Cb.Pv.Att.Gaps
import Cb.Sub.SumOrder

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Cb.Pv.Att
open Iop Prob Hiop Cb IOR TWhole Reduction Cb.Sub

variable {E : Type} [Field E]

/-! ### Two sendings in the middle of a chain, at one signature -/

section Frame
variable {K X Y₁ Y₂ X₃ Wp Wp₁ Wp₂ : Type} {E₁ E₂ E₃ E₄ : ExtSpec} (S₁ N₁ N₂ : Sig E)
  (Sd₁ : N₁.Seeds) (Sd₂ : N₂.Seeds) (L₁ : N₁.O → ℕ) (L₂ : N₂.O → ℕ) (bk₁ : N₁.Msg → Wp₁ → Wp)
  (bk₂ : N₂.Msg → Wp₂ → Wp₁) (R : IOR X E₁ Y₁ E₂) (T₁ : IOR Y₁ E₂ Y₂ E₃) (T₂ : IOR Y₂ E₃ X₃ E₄)

/-- The first three in a row. -/
noncomputable def frame1Red :
    Reduction ((X × S₁.Smp) × (E₁.prod S₁.ext).Str)
      ((Y₂ × (S₁.sum N₁).Smp) × (E₃.prod (S₁.sum N₁).ext).Str) :=
  (R.keep S₁.Smp S₁.ext).red.seq ((ldSendSig S₁ N₁ Sd₁ Y₁ E₂).red.seq
    (T₁.keep (S₁.sum N₁).Smp (S₁.sum N₁).ext).red)

/-- The five in a row. -/
noncomputable def frame2Red :
    Reduction ((X × S₁.Smp) × (E₁.prod S₁.ext).Str)
      ((X₃ × ((S₁.sum N₁).sum N₂).Smp) × (E₄.prod ((S₁.sum N₁).sum N₂).ext).Str) :=
  (frame1Red S₁ N₁ Sd₁ R T₁).seq ((ldSendSig (S₁.sum N₁) N₂ Sd₂ Y₂ E₃).red.seq
    (T₂.keep ((S₁.sum N₁).sum N₂).Smp ((S₁.sum N₁).sum N₂).ext).red)

/-- The errors, in a row: R's, the first sending's, T₁'s, the second sending's, T₂'s. -/
noncomputable def frame2Err (ε₀ : Err R.shape) (ε₁ : Err T₁.shape) (ε₂ : Err T₂.shape) :
    Err (frame2Red S₁ N₁ N₂ Sd₁ Sd₂ R T₁ T₂).shape :=
  Err.app (s := (frame1Red S₁ N₁ Sd₁ R T₁).shape)
    (Err.app ε₀
      (Err.app (s := (ldSendSig S₁ N₁ Sd₁ Y₁ E₂).shape) (ldSendFamErr N₁ Sd₁ L₁, (0, ())) ε₁))
    (Err.app (s := (ldSendSig (S₁.sum N₁) N₂ Sd₂ Y₂ E₃).shape)
      (ldSendFamErr N₂ Sd₂ L₂, (0, ())) ε₂)

/-- The extractor: the parts' in turn. -/
noncomputable def frame2Ext (d : S₁.Wit × Wp) (d' : (S₁.sum N₁).Wit × Wp₁) :
    (X × S₁.Smp) × (E₁.prod S₁.ext).Str → Tr (frame2Red S₁ N₁ N₂ Sd₁ Sd₂ R T₁ T₂).shape →
      ((S₁.sum N₁).sum N₂).Wit × Wp₂ → S₁.Wit × Wp :=
  Reduction.extSeq (frame1Red S₁ N₁ Sd₁ R T₁) _
    (Reduction.extSeq _ _ (fun _ _ w => w)
      (Reduction.extSeq _ _
        (fun _ _ w =>
          (S₁.left N₁ (T := OMsg.Wit) w.1, bk₁ (N₁.msgs (S₁.right N₁ (T := OMsg.Wit) w.1)) w.2))
        (fun _ _ w => w) d) d)
    (Reduction.extSeq _ _
      (fun _ _ w =>
        ((S₁.sum N₁).left N₂ (T := OMsg.Wit) w.1,
          bk₂ (N₂.msgs ((S₁.sum N₁).right N₂ (T := OMsg.Wit) w.1)) w.2))
      (fun _ _ w => w) d') d

variable {S₁ N₁ N₂ Sd₁ Sd₂ L₁ L₂ bk₁ bk₂ R T₁ T₂}

/-- Two sendings in the middle of a chain. -/
theorem frame2 {A : Rels K X E₁ (S₁.Msg × Wp)} {V : Rels K Y₁ E₂ (S₁.Msg × Wp)}
    {Rl₁ : Rels K Y₁ E₂ ((S₁.sum N₁).Msg × Wp₁)} {C₁ : Rels K Y₂ E₃ ((S₁.sum N₁).Msg × Wp₁)}
    {Rl₂ : Rels K Y₂ E₃ (((S₁.sum N₁).sum N₂).Msg × Wp₂)}
    {C₂ : Rels K X₃ E₄ (((S₁.sum N₁).sum N₂).Msg × Wp₂)} {ε₀ : Err R.shape} {ε₁ : Err T₁.shape}
    {ε₂ : Err T₂.shape} (d : S₁.Wit × Wp) (d' : (S₁.sum N₁).Wit × Wp₁)
    (h₀ : KnowAt R A V idW ε₀) (h₁ : KnowAt T₁ Rl₁ C₁ idW ε₁) (h₂ : KnowAt T₂ Rl₂ C₂ idW ε₂)
    (hon₁ : ∀ b, V.on b → Rl₁.on b)
    (hseam₁ : ∀ b m w', Rl₁.relR b (m, w') →
      V.relR b (S₁.left N₁ (T := OMsg.Msg) m, bk₁ (S₁.right N₁ (T := OMsg.Msg) m) w'))
    (hon₂ : ∀ b, C₁.on b → Rl₂.on b)
    (hseam₂ : ∀ b m w', Rl₂.relR b (m, w') →
      C₁.relR b ((S₁.sum N₁).left N₂ (T := OMsg.Msg) m,
        bk₂ ((S₁.sum N₁).right N₂ (T := OMsg.Msg) m) w'))
    (hF₁ : Sd₁.Fair) (hL₁ : ∀ a, (N₁.om a).ListLE (L₁ a)) (hE₁ : ∀ a, (N₁.om a).Evades)
    (hF₂ : Sd₂.Fair) (hL₂ : ∀ a, (N₂.om a).ListLE (L₂ a)) (hE₂ : ∀ a, (N₂.om a).Evades) :
    (frame2Red S₁ N₁ N₂ Sd₁ Sd₂ R T₁ T₂).KnowInto (S₁.over A).on
      (((S₁.sum N₁).sum N₂).over C₂).on (S₁.over A).relR (((S₁.sum N₁).sum N₂).over C₂).relR
      (frame2Ext S₁ N₁ N₂ Sd₁ Sd₂ bk₁ bk₂ R T₁ T₂ d d')
      (frame2Err S₁ N₁ N₂ Sd₁ Sd₂ L₁ L₂ R T₁ T₂ ε₀ ε₁ ε₂) :=
  sum_step (S₁.sum N₁) N₂ Sd₂ L₂ bk₂ d d'
    (sum_order S₁ N₁ Sd₁ L₁ bk₁ d h₀ h₁ hon₁ hseam₁ hF₁ hL₁ hE₁) h₂ hon₂ hseam₂ hF₂ hL₂ hE₂

end Frame

/-! ### A chain at other tuples of messages -/

namespace Ch
variable [Fintype E] {M M' : Type}

/-- A chain at the tuples M, read at tuples M' through π. -/
def atM (π : M' → M) : {X : Type} → Ch E M X → Ch E M' X
  | _, .done X => .done X
  | _, .ride Y n F cl msg L Ow next =>
    .ride Y n F cl (fun m => msg (π m)) (fun x r m => L x r (π m)) (fun b m => Ow b (π m))
      (next.atM π)
  | _, .draw D err P next => .draw D err (fun x m => P x (π m)) (next.atM π)
  | _, .send n D err P L next =>
    .send n D err (fun x m => P x (π m)) (fun x s m => L x s (π m)) (next.atM π)

theorem todo_atM (π : M' → M) : ∀ {X : Type} (c : Ch E M X) (x : X) (m : M'),
    (c.atM π).Todo x m ↔ c.Todo x (π m)
  | _, .done _, _, _ => Iff.rfl
  | _, .ride _ _ _ _ _ _ _ next, x, m =>
    exists_congr fun r => and_congr Iff.rfl (and_congr Iff.rfl
      (exists_congr fun o => todo_atM π next ((x, r), o) m))
  | _, .draw _ _ _ _, _, _ => Iff.rfl
  | _, .send _ _ _ _ _ _, _, _ => Iff.rfl

theorem ok_atM (π : M' → M) : ∀ {X : Type} (c : Ch E M X), c.OK → (c.atM π).OK
  | _, .done _, _ => trivial
  | _, .ride _ _ _ _ _ _ _ next, h =>
    ⟨h.1, fun b m h1 h2 => h.2.1 b (π m) h1 ((todo_atM π next b m).1 h2), ok_atM π next h.2.2⟩
  | _, .draw _ _ _ next, h =>
    ⟨fun x m hP => le_trans (cnt_mono fun β hβ => (todo_atM π next (x, β) m).1 hβ)
      (h.1 x (π m) hP), ok_atM π next h.2⟩
  | _, .send _ _ _ _ _ next, h =>
    ⟨fun x m hP s hL => le_trans (cnt_mono fun β hβ => (todo_atM π next ((x, s), β) m).1 hβ)
      (h.1 x (π m) hP s hL), ok_atM π next h.2⟩

end Ch

/-! ### A sub-proof's link -/

section Link
variable [Fintype E] {M : Type} {J₁ J₂ : Type} [Fintype J₁] [Fintype J₂] {X₀ X : Type}
  {Ex : ExtSpec}

/-- The lookup, the chain of the sub-proof's own rounds, and the ledger of the verifier's claims
laid beside the chain's last statement. -/
noncomputable def subR (R₁ : IOR X₀ Ex X Ex) (c : Ch E M X) (cl : c.End → Ledger E (J₁ ⊕ J₂)) :
    IOR X₀ Ex (c.End × Ledger E (J₁ ⊕ J₂)) Ex :=
  (R₁.seq (c.R Ex)).post (fun e => some (e, cl e)) (ExtMap.id Ex)

/-- A lookup with a joint B₁ of its own behind it: if the chain's claim at its start gives B₁, the
lookup ends at the chain's claim. -/
theorem look_seam {K X0 Wp : Type} {R₁ : IOR X₀ Ex X Ex} {A : Rels K X₀ Ex (M × Wp)}
    {B₁ : Rels K X Ex (M × Wp)} {ε₁ : Err R₁.shape} (A0 : Rels K X0 Ex (M × Wp)) (pr : X → X0)
    (G : X → M → Prop) (h : KnowAt R₁ A B₁ idW ε₁) (hon : ∀ b, B₁.on b → (jt A0 pr G).on b)
    (hrel : ∀ b w, B₁.on b → (jt A0 pr G).relR b w → B₁.relR b w) :
    KnowAt R₁ A (jt A0 pr G) idW ε₁ :=
  knowAt_mono h (fun _ ha => ha) (fun _ _ _ hw => hw) hrel hon

/-- From the lookup's joint to: B₀, and the ledger's pull-back to the early entries holds. -/
theorem subR_knowAt {K X0 Wp : Type} {R₁ : IOR X₀ Ex X Ex} {A : Rels K X₀ Ex (M × Wp)}
    {ε₁ : Err R₁.shape} (c : Ch E M X) (hc : c.OK) (A0 : Rels K X0 Ex (M × Wp)) (pr : X → X0)
    (Dn : X → M → Prop)
    (hLook : KnowAt R₁ A (jt A0 pr fun x m => Dn x m ∧ c.Todo x m) idW ε₁)
    (cl : c.End → Ledger E (J₁ ⊕ J₂)) (a : c.End → J₂ → Aff E J₁) (msg₁ : M → J₁ → E) (n : ℕ)
    (hn : ∀ e, (cl e).length ≤ n) (B₀ : Rels K c.End Ex (M × Wp))
    (hOn : ∀ e y, A0.on (pr (c.back e), y) → B₀.on (e, y))
    (hEnd : ∀ e y w, A0.on (pr (c.back e), y) → B₀.relR (e, y) w →
      Ledger.Holds (pullL (a e) (cl e)) (msg₁ w.1) →
        A0.relR (pr (c.back e), y) w ∧ c.Last Dn e w.1) :
    KnowAt (subR R₁ c cl) A (virtJ B₀ a msg₁ n) idW (Err.app ε₁ (c.eps Ex)) :=
  knowAt_postMap (B' := virtJ B₀ a msg₁ n) (fun e => (e, cl e))
    (knowAt_seq hLook (Ch.knowAt Ex A0 c pr Dn hc))
    (fun e y he => ⟨hOn e y he, hn e⟩) fun e y w he hw => hEnd e y w he hw.1 hw.2

/-- THE STATEMENT: the link of a sub-proof as a whole. -/
theorem sub_link {K X0 Y₂ X₃ Wp Wp₁ Wp₂ : Type} (S₁ N₁ N₂ : Sig E) (Sd₁ : N₁.Seeds)
    (Sd₂ : N₂.Seeds) (L₁ : N₁.O → ℕ) (L₂ : N₂.O → ℕ) (bk₁ : N₁.Msg → Wp₁ → Wp)
    (bk₂ : N₂.Msg → Wp₂ → Wp₁) {R₁ : IOR X₀ Ex X Ex} {A : Rels K X₀ Ex (S₁.Msg × Wp)}
    {ε₁ : Err R₁.shape} (c : Ch E S₁.Msg X) (hc : c.OK) (A0 : Rels K X0 Ex (S₁.Msg × Wp))
    (pr : X → X0) (Dn : X → S₁.Msg → Prop)
    (hLook : KnowAt R₁ A (jt A0 pr fun x m => Dn x m ∧ c.Todo x m) idW ε₁)
    (cl : c.End → Ledger E (J₁ ⊕ J₂)) (a : c.End → J₂ → Aff E J₁) (msg₁ : S₁.Msg → J₁ → E)
    (ent : N₁.Msg → J₂ → E) (n : ℕ) (hn : ∀ e, (cl e).length ≤ n)
    (B₀ : Rels K c.End Ex (S₁.Msg × Wp))
    (hOn : ∀ e y, A0.on (pr (c.back e), y) → B₀.on (e, y))
    (hEnd : ∀ e y w, A0.on (pr (c.back e), y) → B₀.relR (e, y) w →
      Ledger.Holds (pullL (a e) (cl e)) (msg₁ w.1) →
        A0.relR (pr (c.back e), y) w ∧ c.Last Dn e w.1)
    {T₁ : IOR (c.End × Ledger E (J₁ ⊕ J₂)) Ex Y₂ Ex} {T₂ : IOR Y₂ Ex X₃ Ex}
    {Rl₁ : Rels K (c.End × Ledger E (J₁ ⊕ J₂)) Ex ((S₁.sum N₁).Msg × Wp₁)}
    {C₁ : Rels K Y₂ Ex ((S₁.sum N₁).Msg × Wp₁)}
    {Rl₂ : Rels K Y₂ Ex (((S₁.sum N₁).sum N₂).Msg × Wp₂)}
    {C₂ : Rels K X₃ Ex (((S₁.sum N₁).sum N₂).Msg × Wp₂)} {η₁ : Err T₁.shape} {η₂ : Err T₂.shape}
    (hRng : KnowAt T₁ Rl₁ C₁ idW η₁) (hDig : KnowAt T₂ Rl₂ C₂ idW η₂)
    (ho₁ : ∀ b, (virtJ B₀ a msg₁ n).on b → Rl₁.on b)
    (hs₁ : ∀ b m w', Rl₁.relR b (m, w') →
      B₀.relR (b.1.1, b.2) (S₁.left N₁ (T := OMsg.Msg) m, bk₁ (S₁.right N₁ (T := OMsg.Msg) m) w') ∧
        Agree (a b.1.1) (msg₁ (S₁.left N₁ (T := OMsg.Msg) m))
          (ent (S₁.right N₁ (T := OMsg.Msg) m)) ∧
        Ledger.Holds b.1.2 (Sum.elim (msg₁ (S₁.left N₁ (T := OMsg.Msg) m))
          (ent (S₁.right N₁ (T := OMsg.Msg) m))))
    (ho₂ : ∀ b, C₁.on b → Rl₂.on b)
    (hs₂ : ∀ b m w', Rl₂.relR b (m, w') →
      C₁.relR b ((S₁.sum N₁).left N₂ (T := OMsg.Msg) m,
        bk₂ ((S₁.sum N₁).right N₂ (T := OMsg.Msg) m) w'))
    (d : S₁.Wit × Wp) (d' : (S₁.sum N₁).Wit × Wp₁)
    (hF₁ : Sd₁.Fair) (hL₁ : ∀ i, (N₁.om i).ListLE (L₁ i)) (hE₁ : ∀ i, (N₁.om i).Evades)
    (hF₂ : Sd₂.Fair) (hL₂ : ∀ i, (N₂.om i).ListLE (L₂ i)) (hE₂ : ∀ i, (N₂.om i).Evades) :
    (frame2Red S₁ N₁ N₂ Sd₁ Sd₂ (subR R₁ c cl) T₁ T₂).KnowInto (S₁.over A).on
      (((S₁.sum N₁).sum N₂).over C₂).on (S₁.over A).relR (((S₁.sum N₁).sum N₂).over C₂).relR
      (frame2Ext S₁ N₁ N₂ Sd₁ Sd₂ bk₁ bk₂ (subR R₁ c cl) T₁ T₂ d d')
      (frame2Err S₁ N₁ N₂ Sd₁ Sd₂ L₁ L₂ (subR R₁ c cl) T₁ T₂ (Err.app ε₁ (c.eps Ex)) η₁ η₂) :=
  frame2 d d' (subR_knowAt c hc A0 pr Dn hLook cl a msg₁ n hn B₀ hOn hEnd) hRng hDig ho₁
    (fun b m w' hw => by
      obtain ⟨g1, g2, g3⟩ := hs₁ b m w' hw
      exact ⟨g1, (late_holds (a b.1.1) b.1.2 _ _ g2).1 g3⟩)
    ho₂ hs₂ hF₁ hL₁ hE₁ hF₂ hL₂ hE₂

/-- The last block cut in two: a block D that ends at a ledger on entries J₃ with nothing left open
beside it, and the draw that batches the ledger into one form. -/
theorem dig_batch {K Y₂ X' M₃ Wp₂ J₃ : Type} [Fintype J₃] {D : IOR Y₂ Ex (X' × Ledger E J₃) Ex}
    {Rl₂ : Rels K Y₂ Ex (M₃ × Wp₂)} {B₂ : Rels K X' Ex (M₃ × Wp₂)} {η : Err D.shape}
    (msg₃ : M₃ → J₃ → E) (n₃ : ℕ) (hD : KnowAt D Rl₂ (ledJ B₂ msg₃ n₃) idW η)
    (h0 : ∀ b w, B₂.relR b w) :
    KnowAt (D.seq (IOR.draw E (ledNx (J := J₃) (P := X')) Ex)) Rl₂ (ledOut Ex msg₃ B₂.core) idW
      (Err.app η (Nums.draw K E (ledNx (J := J₃) (P := X')) Ex (n₃ - 1)).err) :=
  led_batch msg₃ n₃ hD h0

/-- The chain of an attention sub-proof's own rounds. -/
noncomputable abbrev linkCh (units : List (SumL E M (Seen E X))) (T : TailG E M (Seen E X)) :
    Ch E M X := (AttOwn.mk units T.toTail).ch

/-- Its conditions hold. -/
theorem linkCh_ok (units : List (SumL E M (Seen E X))) (T : TailG E M (Seen E X)) :
    (linkCh units T).OK := attOwn_ok (AttOwn.mk units T.toTail) T.laws

end Link
end Cb.Pv.Att
