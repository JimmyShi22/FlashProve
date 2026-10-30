-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/FoldKeeps.lean: a general rule on the fold over blocks; no kind is named. A relation R
on the carried record that is reflexive and transitive, and that every block keeps (the record that
the block returns is related to the one that it was handed), is kept by the fold over a list of
blocks, by a link's and a chain's flat list, by a chain's decision and by a file's. Theorems.

  Decides R b, Fn R f, FnCl R f   a block's decide, a change of the record, a run of claims keeps R.
  Whole R b             decide, every run of claims and every run behind the batching keep R.
  claimsIn_keeps, afterIn_keeps   the link's gathered runs keep R where the hearing blocks do.
  LinkKeeps R L, link_flat_keeps  what is asked of a link's parts; then every block of its flat list
                        keeps R. Of the batching: it keeps R whenever the function that it is handed
                        does.
  ChainKeeps R c, chain_flat_keeps   the like of a chain.
  foldBlocks_keeps, chainAt_keeps    the fold and the chain's decision keep R.
  foldBlocks_split      a fold over two lists in a row that says yes is a fold over the first, and
                        from what that returns a fold over the second.
  chainAt_border        at every border of a chain whose decision says yes: the record there is
                        related to the first record, and the last record to it.
  run_keeps             a file's decision: each chain's last record is related to its first.
  keeps_of_inv          a property that every block keeps, as such a relation.
What is not claimed. That any block of the protocol keeps any relation: that is each kind's own
matter. Nothing on soundness, on an honest prover or on hiding.

-/
import Johnson.Desc.ChainEndFold
import Johnson.Desc.BlockLaws

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Keeps
open VerifiableInference.Desc

variable {S Cl : Type}

/-- A block's decide keeps R. -/
def Decides (R : S → S → Prop) (b : Block S Cl) : Prop :=
  ∀ s rs gs s', b.decide s rs gs = .ok s' → R s s'

/-- A change of the record, which may refuse, keeps R. -/
def Fn (R : S → S → Prop) (f : S → Except String S) : Prop := ∀ s s', f s = .ok s' → R s s'

/-- A run of claims keeps R. -/
def FnCl (R : S → S → Prop) (f : S → Except String (List Cl × S)) : Prop :=
  ∀ s y, f s = .ok y → R s y.2

/-- A block's decide, each of its runs of claims and each of its runs behind the batching keep R. -/
def Whole (R : S → S → Prop) (b : Block S Cl) : Prop :=
  Decides R b ∧ (∀ c ∈ b.claims, ∀ n, FnCl R (c.2 n)) ∧ ∀ c ∈ b.after, Fn R c.2

/-- A bind of Except that returns: both halves return. -/
theorem ebind_ok {α β : Type} {x : Except String α} {f : α → Except String β} {b : β}
    (h : x.bind f = .ok b) : ∃ a, x = .ok a ∧ f a = .ok b := by
  cases x with
  | error e => cases h
  | ok a => exact ⟨a, rfl, h⟩

/-- A named value that is there. -/
theorem named_ok {α : Type} {n : String} {o : Option α} {x : α} (h : named n o = .ok x) :
    o = some x := by
  cases o with
  | none => cases h
  | some y => cases h; rfl

/-- What a lookup in a list of pairs finds is a member of the list. -/
theorem lookup_mem {α β : Type} [BEq α] (a : α) (y : β) (l : List (α × β))
    (h : l.lookup a = some y) : ∃ a', (a', y) ∈ l := by
  induction l with
  | nil => cases h
  | cons p l ih =>
    obtain ⟨k, v⟩ := p
    simp only [List.lookup] at h
    split at h
    · injection h with h
      subst h
      exact ⟨k, List.mem_cons_self⟩
    · obtain ⟨a', ha⟩ := ih h
      exact ⟨a', List.mem_cons_of_mem _ ha⟩

/-- One step of the gathering of a link's claims. -/
def stepC (bs : List (Block S Cl)) (acc : Except String (List Cl × S)) (o : Nat × String) :
    Except String (List Cl × S) :=
  acc.bind fun x =>
    (named (o.2 ++ ": no such run") ((bs[o.1]?).bind fun b => b.claims.lookup o.2)).bind fun run =>
      match run x.1.length x.2 with
      | .ok y => .ok (x.1 ++ y.1, y.2)
      | .error e => .error (o.2 ++ ": " ++ e)

/-- The runs of claims of a list of blocks, as a fold over the order. -/
theorem claimsIn_eq (bs : List (Block S Cl)) (order : List (Nat × String)) (s : S) :
    claimsIn bs order s = order.foldl (stepC bs) (.ok ([], s)) := rfl

/-- One step of the runs behind the batching. -/
def stepA (bs : List (Block S Cl)) (acc : Except String S) (o : Nat × String) : Except String S :=
  acc.bind fun x =>
    (named (o.2 ++ ": no such run") ((bs[o.1]?).bind fun b => b.after.lookup o.2)).bind fun run =>
      match run x with
      | .ok y => .ok y
      | .error e => .error (o.2 ++ ": " ++ e)

/-- The runs behind the batching of a list of blocks, as a fold over the order. -/
theorem afterIn_eq (bs : List (Block S Cl)) (order : List (Nat × String)) (s : S) :
    afterIn bs order s = order.foldl (stepA bs) (.ok s) := rfl

section rule
variable (R : S → S → Prop) (hr : ∀ s, R s s) (ht : ∀ a b c, R a b → R b c → R a c)
include hr ht

/-- The link's gathered claims keep R where the hearing blocks do. -/
theorem claimsIn_keeps (bs : List (Block S Cl)) (hb : ∀ b ∈ bs, Whole R b)
    (order : List (Nat × String)) : FnCl R (claimsIn bs order) := by
  intro s y h
  rw [claimsIn_eq] at h
  have key : ∀ (order : List (Nat × String)) (acc : Except String (List Cl × S)),
      (∀ x, acc = .ok x → R s x.2) → ∀ y, order.foldl (stepC bs) acc = .ok y → R s y.2 := by
    intro order
    induction order with
    | nil => intro acc ha y hy; exact ha y hy
    | cons o os ih =>
      intro acc ha y hy
      refine ih (stepC bs acc o) ?_ y hy
      intro x hx
      obtain ⟨a, haa, h1⟩ := ebind_ok hx
      obtain ⟨run, hrun, h2⟩ := ebind_ok h1
      have ho := named_ok hrun
      cases hq : bs[o.1]? with
      | none => simp [hq] at ho
      | some b =>
        simp only [hq, Option.bind_some] at ho
        obtain ⟨n, hn⟩ := lookup_mem _ _ _ ho
        cases hy' : run a.1.length a.2 with
        | error e => simp [hy'] at h2
        | ok z =>
          simp only [hy', Except.ok.injEq] at h2
          subst h2
          exact ht _ a.2 _ (ha a haa)
            ((hb b (List.mem_of_getElem? hq)).2.1 (n, run) hn a.1.length a.2 z hy')
  exact key order _ (fun x hx => by cases hx; exact hr s) y h

/-- The runs behind the batching keep R where the hearing blocks do. -/
theorem afterIn_keeps (bs : List (Block S Cl)) (hb : ∀ b ∈ bs, Whole R b)
    (order : List (Nat × String)) : Fn R (afterIn bs order) := by
  intro s y h
  rw [afterIn_eq] at h
  have key : ∀ (order : List (Nat × String)) (acc : Except String S),
      (∀ x, acc = .ok x → R s x) → ∀ y, order.foldl (stepA bs) acc = .ok y → R s y := by
    intro order
    induction order with
    | nil => intro acc ha y hy; exact ha y hy
    | cons o os ih =>
      intro acc ha y hy
      refine ih (stepA bs acc o) ?_ y hy
      intro x hx
      obtain ⟨a, haa, h1⟩ := ebind_ok hx
      obtain ⟨run, hrun, h2⟩ := ebind_ok h1
      have ho := named_ok hrun
      cases hq : bs[o.1]? with
      | none => simp [hq] at ho
      | some b =>
        simp only [hq, Option.bind_some] at ho
        obtain ⟨n, hn⟩ := lookup_mem _ _ _ ho
        cases hy' : run a with
        | error e => simp [hy'] at h2
        | ok z =>
          simp only [hy', Except.ok.injEq] at h2
          subst h2
          exact ht _ _ _ (ha a haa) ((hb b (List.mem_of_getElem? hq)).2.2 _ hn _ _ hy')
  exact key order _ (fun x hx => by cases hx; exact hr s) y h

/-- What is asked of a link's parts. -/
def LinkKeeps (L : Link S Cl) : Prop :=
  Fn R L.lay ∧ (∀ b ∈ L.hear, Whole R b) ∧ (∀ f, FnCl R f → Decides R (L.batch f)) ∧
    (∀ b ∈ L.close, Decides R b) ∧ Fn R L.clear

/-- Every block of a link's flat list keeps R. -/
theorem link_flat_keeps (L : Link S Cl) (h : LinkKeeps R L) : ∀ b ∈ L.blocksInOrder, Decides R b := by
  obtain ⟨hl, hh, hbt, hc, hcl⟩ := h
  intro b hb
  unfold Link.blocksInOrder at hb
  rcases List.mem_append.1 hb with h | h
  · rcases List.mem_append.1 h with h | h
    · rcases List.mem_append.1 h with h | h
      · rcases List.mem_cons.1 h with rfl | h
        · exact fun s _ _ s' hd => hl s s' hd
        · exact (hh b h).1
      · rcases List.mem_cons.1 h with rfl | h
        · exact hbt _ fun s y hy => claimsIn_keeps R hr ht L.hear hh L.order s y
            (claimsIn_of_claimsInBy L.each L.hear L.order s y hy)
        · rcases List.mem_cons.1 h with rfl | h
          · intro s _ _ s' hd
            have hd' : L.runBehind s = .ok s' := hd
            unfold Link.runBehind at hd'
            cases ht' : L.tests s with
            | error e => simp [ht'] at hd'
            | ok _ =>
              simp only [ht'] at hd'
              exact afterIn_keeps R hr ht L.hear hh L.orderAfter s s' hd'
          · cases h
    · exact hc b h
  · rcases List.mem_cons.1 h with rfl | h
    · exact fun s _ _ s' hd => hcl s s' hd
    · cases h

/-- What is asked of a chain's parts. -/
def ChainKeeps (c : Chain S Cl) : Prop :=
  Decides R c.first ∧ (∀ b ∈ c.front, Decides R b) ∧ (∀ L ∈ c.links, LinkKeeps R L) ∧
    (∀ b ∈ c.back, Decides R b) ∧ Decides R c.last

/-- Every block of a chain's flat list keeps R. -/
theorem chain_flat_keeps (c : Chain S Cl) (h : ChainKeeps R c) : ∀ b ∈ c.blocksInOrder, Decides R b := by
  obtain ⟨h1, hf, hl, hk, h9⟩ := h
  intro b hb
  dsimp only [Chain.blocksInOrder] at hb
  rcases List.mem_append.1 hb with h | h
  · rcases List.mem_append.1 h with h | h
    · rcases List.mem_append.1 h with h | h
      · rcases List.mem_cons.1 h with rfl | h
        · exact h1
        · obtain ⟨b', hb', rfl⟩ := List.mem_map.1 h
          exact hf b' hb'
      · obtain ⟨L, hL, hbL⟩ := List.mem_flatMap.1 h
        exact link_flat_keeps R hr ht L (hl L hL) b hbL
    · obtain ⟨b', hb', rfl⟩ := List.mem_map.1 h
      exact hk b' hb'
  · obtain rfl := List.mem_singleton.1 h
    exact h9

/-- The fold over blocks that keep R keeps R. -/
theorem foldBlocks_keeps (ft : Nat) : ∀ (bs : List (Block S Cl)), (∀ b ∈ bs, Decides R b) →
    ∀ (s : S) (rs : List Fmt.RoundView) (cols : List OpenedColumn) (r : S × List Fmt.RoundView × List OpenedColumn),
      foldBlocks ft bs s rs cols = .ok r → R s r.1 := by
  intro bs
  induction bs with
  | nil =>
    intro _ s rs cols r h
    simp only [foldBlocks, Except.ok.injEq] at h
    subst h
    exact hr s
  | cons b l ih =>
    intro hb s rs cols r h
    simp only [foldBlocks] at h
    split at h
    · cases h
    · split at h
      · cases h
      · rename_i s' k hs
        obtain ⟨rs', gs', hd⟩ := ChainEnd.step_decide ft b s s' _ cols k hs
        exact ht _ _ _ (hb b List.mem_cons_self _ _ _ _ hd)
          (ih (fun x hx => hb x (List.mem_cons_of_mem _ hx)) _ _ _ _ h)

end rule

/-- A fold over two lists in a row that says yes: a fold over the first, then over the second. -/
theorem foldBlocks_split (ft : Nat) (l₂ : List (Block S Cl)) : ∀ (l₁ : List (Block S Cl)) (s : S)
    (rs : List Fmt.RoundView) (cols : List OpenedColumn) (r : S × List Fmt.RoundView × List OpenedColumn),
    foldBlocks ft (l₁ ++ l₂) s rs cols = .ok r →
    ∃ t rs' cols', foldBlocks ft l₁ s rs cols = .ok (t, rs', cols') ∧
      foldBlocks ft l₂ t rs' cols' = .ok r := by
  intro l₁
  induction l₁ with
  | nil => intro s rs cols r h; exact ⟨s, rs, cols, rfl, h⟩
  | cons b l ih =>
    intro s rs cols r h
    simp only [List.cons_append, foldBlocks] at h ⊢
    split at h
    · cases h
    · split at h
      · cases h
      · rename_i hc _ s' k hs
        obtain ⟨t, rs', cols', h1, h2⟩ := ih _ _ _ _ h
        refine ⟨t, rs', cols', ?_, h2⟩
        simp only [if_neg hc]
        exact h1

/-- What a chain's decision rests on: a fold that leaves nothing over. -/
theorem chainAt_fold (name : String) (ft : Nat) (bs : List (Block S Cl)) (s s' : S) (v : Fmt.View)
    (h : chainAt name ft bs s v = .ok s') :
    foldBlocks ft bs s v.rounds v.opened = .ok (s', [], []) := by
  unfold chainAt at h
  split at h
  · cases h
  · split at h
    · rename_i t hf
      injection h with h
      subst h
      exact hf
    · cases h
    · cases h

section rule2
variable (R : S → S → Prop) (hr : ∀ s, R s s) (ht : ∀ a b c, R a b → R b c → R a c)
include hr ht

/-- A chain's decision over blocks that keep R keeps R. -/
theorem chainAt_keeps (name : String) (ft : Nat) (bs : List (Block S Cl))
    (hb : ∀ b ∈ bs, Decides R b) (s s' : S) (v : Fmt.View)
    (h : chainAt name ft bs s v = .ok s') : R s s' :=
  foldBlocks_keeps R hr ht ft bs hb s _ _ _ (chainAt_fold name ft bs s s' v h)

/-- **At every border**: the record there is related to the first, and the last to it. -/
theorem chainAt_border (name : String) (ft : Nat) (l₁ l₂ : List (Block S Cl))
    (hb : ∀ b ∈ l₁ ++ l₂, Decides R b) (s s' : S) (v : Fmt.View)
    (h : chainAt name ft (l₁ ++ l₂) s v = .ok s') :
    ∃ t rs cols, foldBlocks ft l₁ s v.rounds v.opened = .ok (t, rs, cols) ∧ R s t ∧ R t s' := by
  obtain ⟨t, rs, cols, h1, h2⟩ :=
    foldBlocks_split ft l₂ l₁ s _ _ _ (chainAt_fold name ft _ s s' v h)
  exact ⟨t, rs, cols, h1,
    foldBlocks_keeps R hr ht ft l₁ (fun b hx => hb b (List.mem_append_left _ hx)) _ _ _ _ h1,
    foldBlocks_keeps R hr ht ft l₂ (fun b hx => hb b (List.mem_append_right _ hx)) _ _ _ _ h2⟩

end rule2

/-- **A file's decision**: each chain's last record is related to its first. -/
theorem run_keeps {Xi : Type} (F : FileDescription Xi) (R₁ : F.S₁ → F.S₁ → Prop)
    (R₂ : F.S₂ → F.S₂ → Prop) (R₃ : F.S₃ → F.S₃ → Prop)
    (r₁ : ∀ s, R₁ s s) (t₁ : ∀ a b c, R₁ a b → R₁ b c → R₁ a c)
    (r₂ : ∀ s, R₂ s s) (t₂ : ∀ a b c, R₂ a b → R₂ b c → R₂ a c)
    (r₃ : ∀ s, R₃ s s) (t₃ : ∀ a b c, R₃ a b → R₃ b c → R₃ a c)
    (k₁ : ChainKeeps R₁ F.first) (k₂ : ChainKeeps R₂ F.shared) (k₃ : ChainKeeps R₃ F.second)
    (x : Xi) (v₁ v₂ v₃ : Fmt.View) (h : F.run x v₁ v₂ v₃ = true) :
    ∃ e₁ e₂ e₃ s₃, F.runEnd x v₁ v₂ v₃ = .ok (e₁, e₂, e₃) ∧
      F.start₃ (F.pub x) e₁ e₂ = .ok s₃ ∧ R₁ (F.start₁ (F.pub x)) e₁ ∧
      R₂ (F.start₂ (F.pub x)) e₂ ∧ R₃ s₃ e₃ := by
  unfold FileDescription.run at h
  cases hq : F.runEnd x v₁ v₂ v₃ with
  | error e => simp [hq, Except.isOk, Except.toBool] at h
  | ok r =>
    obtain ⟨e₁, e₂, e₃⟩ := r
    have hq' := hq
    unfold FileDescription.runEnd at hq'
    obtain ⟨j₁, j₂, ⟨s₃, j₀, j₃⟩, _⟩ :=
      ChainEnd.runCore_chains _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hq'
    exact ⟨e₁, e₂, e₃, s₃, rfl, j₀,
      chainAt_keeps R₁ r₁ t₁ _ _ _ (chain_flat_keeps R₁ r₁ t₁ _ k₁) _ _ _ j₁,
      chainAt_keeps R₂ r₂ t₂ _ _ _ (chain_flat_keeps R₂ r₂ t₂ _ k₂) _ _ _ j₂,
      chainAt_keeps R₃ r₃ t₃ _ _ _ (chain_flat_keeps R₃ r₃ t₃ _ k₃) _ _ _ j₃⟩

/-- A property of the record, as a relation: if it held in front, it holds behind. -/
def ofInv (P : S → Prop) : S → S → Prop := fun s s' => P s → P s'

/-- The relation made of a property is reflexive. -/
theorem ofInv_refl (P : S → Prop) (s : S) : ofInv P s s := id

/-- The relation made of a property is transitive. -/
theorem ofInv_trans (P : S → Prop) (a b c : S) (h : ofInv P a b) (k : ofInv P b c) :
    ofInv P a c := fun x => k (h x)

/-- A property that every block of a chain keeps holds at the end if it held at the start. -/
theorem keeps_of_inv (P : S → Prop) (name : String) (ft : Nat) (bs : List (Block S Cl))
    (hb : ∀ b ∈ bs, Decides (ofInv P) b) (s s' : S) (v : Fmt.View)
    (h : chainAt name ft bs s v = .ok s') (h0 : P s) : P s' :=
  chainAt_keeps (ofInv P) (ofInv_refl P) (ofInv_trans P) name ft bs hb s s' v h h0

end VerifiableInference.Desc.Keeps
