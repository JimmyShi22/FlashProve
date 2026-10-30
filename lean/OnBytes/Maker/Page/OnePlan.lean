-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Maker/Page/OnePlan.lean: what the key file's chains and the proof file's chains of one call
have in common: the digest of the public files, the field, the shape of the stored tables, the
number of bytes of a salt, and the number of bytes of a salt in the binding tree.

The sentence at a key file lays its letters at the key's one-time chain, the sentence at a proof
file at the proof's first chain. To use both at one object the two chains must agree. Inside a file
the readers' own test gives one setting (`sameSetting_open`, OnBytes/TieK/ChainsRead.lean;
OnBytes/Maker/Page/GoodFields.lean). Here are the equations between the two files.

Where they come from. The digest and the tables' shape: `Tie.SameChains`
(OnBytes/Tie/SameChains.lean). The field: the two checks' own tests. The two numbers of bytes: both
chains' parameter bytes are spelled from plans and items that `Params.configure` makes at one
setting, that of the parameter file's lines (`configure_bytes`, OnBytes/Model/ReadBackMade.lean;
`configure_plans`, `configure_proofPlans`, OnBytes/Plan/), and the readers return the words as they
were spelled. OnBytes/Model/ReadBackMade.lean has the whole plan read back where the made plan
passes a test on its words; here that test is not asked, and of the plan the one word alone is read.

Main theorems.
  `cfg_one`: the one-time chain and the first chain hold one digest of the public files.
  `index_one`: the shared chains of the two files hold one shape of the stored tables.
  `fits_proof_of_key`: so a table's key that fits that shape at the key file fits it at the proof
    file.
  `field_one`: both chains hold the field in which the program computes, where the program has said
    yes.
  `rdPlan_salt`, `given_salt`: the plan that is read back from spelled bytes has the word of the
    salt as it was spelled.
  `readBinding_salt`, `spellBinding_at`: the same of the item "binding tree".
  `salt_one`, `bindingSalt_one`: the two equations, for the chains that the planner gives, if the
    parameter bytes of the one-time chain and of the first chain are fewer than 2 ^ 64.
  `salts_port`: both, where the program has said yes.
No letter stands under "there is" but in `planned_made` and `configure_salts`. In `configure_salts`
each stands with the equations that hold it. In `planned_made` the lines, the shapes and the bits
stand as the arguments of one call of `Params.configure` and are tied to nothing else.
No other file calls `cfg_one`, `index_one`, `fits_proof_of_key` or `field_one`.

What is not claimed. What the two numbers are. Nothing on the other words of the plans. Nothing on
soundness.


-/
import OnBytes.Maker.Page.GoodFields
import OnBytes.Maker.Page.PortReads
import OnBytes.TieK.HolesOfChains
import OnBytes.Model.ReadBackMade
import OnBytes.Params.HoldsLaws

set_option autoImplicit false

namespace OnBytes.Maker.Page

open OnBytes.Params Fmt

section Same
variable {p : Model.Verify.Planned} {d : ByteArray}

/-- The one-time chain and the first chain hold one digest of the public files. -/
theorem cfg_one (h : Tie.SameChains p d) :
    p.chains.key.oneTime.given.cfg = p.chains.proof.first.given.cfg :=
  h.1.2.1.trans h.1.2.2.2.2.2.1.symm

/-- The shared chains of the two files hold one shape of the stored tables. -/
theorem index_one (h : Tie.SameChains p d) (t t' : Params.TableName) :
    (Key.tailPublic p.chains.key t).lin.fold.index =
      (Proof.tailPublic p.chains.proof t').lin.fold.index :=
  h.2.1.2.1.trans h.2.1.2.2.2.symm

/-- A table's key that fits the tables' shape at the key file fits it at the proof file. -/
theorem fits_proof_of_key (h : Tie.SameChains p d) (κ : TableKey) (t t' : Params.TableName)
    (hf : κ.fits (Key.tailPublic p.chains.key t).lin.fold.index = true) :
    κ.fits (Proof.tailPublic p.chains.proof t').lin.fold.index = true :=
  index_one h t t' ▸ hf

/-- **One field**, where the program has said yes. -/
theorem field_one {F : K.Files} {id : String} {table further : Params.TableName}
    (h : K.PortYesAt F id table further)
    (hp : Model.Verify.planned F.pol F.KL (some F.lay) = .ok p) :
    p.chains.key.oneTime.given.plan.field = .two ∧
      p.chains.proof.first.given.plan.field = .two := by
  obtain ⟨p₁, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hp₁, -, -, -, hf₁, -⟩ :=
    TieK.port_key_chains F id table further h
  obtain ⟨p₂, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hp₂, -, -, -, hf₂, -⟩ :=
    TieK.port_proof_chains F id table further h
  obtain rfl : p₁ = p := Except.ok.inj (hp₁.symm.trans hp)
  obtain rfl : p₂ = p₁ := Except.ok.inj (hp₂.symm.trans hp)
  rw [Bool.or_eq_false_iff] at hf₂
  exact ⟨by simpa using hf₁, by simpa using hf₂.1⟩

end Same

/-! ## The word of the salt, read back -/

/-- The plan that the reader returns where a plan's spelling begins has the word of the salt as it
was spelled. -/
theorem rdPlan_salt {P P' : Plan} {pre post : ByteArray} {k : ℕ}
    (h : rdPlan (pre ++ P.bytes ++ post) pre.size = some (P', k)) :
    P'.salt = (UInt64.ofNat P.salt).toNat := by
  rw [plan_bytes] at h
  have a := undoes_many undoes_word (P.words.map UInt64.ofNat) (fun _ _ => trivial) pre
    (cat (P.entries.map Entry.bytes) ++ post)
  have e1 : pre ++
        (cat ((P.words.map UInt64.ofNat).map u64) ++ cat (P.entries.map Entry.bytes)) ++ post =
      pre ++ cat ((P.words.map UInt64.ofNat).map u64) ++
        (cat (P.entries.map Entry.bytes) ++ post) := by
    simp only [ByteArray.append_assoc]
  have hw : (P.words.map UInt64.ofNat).length = 8 := rfl
  rw [hw] at a
  generalize cat ((P.words.map UInt64.ofNat).map u64) = W at a e1 h
  unfold rdPlan at h
  rw [e1, a] at h
  simp only [Plan.words, List.map_cons, List.map_nil, fldOf_num] at h
  split at h
  · obtain ⟨x, -, h2⟩ := Option.map_eq_some_iff.1 h
    cases h2
    rfl
  · cases h

/-- The same for `Given.read`, the program's reader of parameter bytes. Conditions as in
`paramsRead_form` (OnBytes/Params/ReadBackAt.lean). -/
theorem given_salt {P : Plan} {c : ByteArray} {I : List (String × ByteArray)} {g : Given}
    (hb : (paramsBytes P c I).size < 2 ^ 64) (hc : c.size = 32)
    (ho : ∀ y ∈ I, okName y.1 = true) (h : Given.read (paramsBytes P c I) = some g) :
    g.plan.salt = (UInt64.ofNat P.salt).toNat := by
  unfold Given.read at h
  rw [paramsReadT_eq] at h
  cases hp : paramsRead (paramsBytes P c I) with
  | none =>
    rw [hp] at h
    cases h
  | some x =>
    rw [hp] at h
    simp only [Option.bind_some] at h
    split at h
    · cases h
      rw [paramsRead_form hb hc ho] at hp
      obtain ⟨y, hy, h2⟩ := Option.bind_eq_some_iff.1 hp
      split at h2
      · cases h2
        exact rdPlan_salt hy
      · cases h2
    · cases h

/-- What is read from an item "binding tree" has, as its number of bytes of a salt, the item's
second word. -/
theorem readBinding_salt {v : ByteArray} {x : LinBindingShape} (h : readBinding v = some x) :
    x.saltBytes = (wordAt v (u64n 0).size).toNat := by
  unfold readBinding Cut.whole Fmt.whole Cut.rd at h
  split at h
  · rename_i y j hy
    split at h
    · cases h
      unfold bindingShape at hy
      obtain ⟨n1, j1, h1, hy⟩ := cut_bind hy
      obtain ⟨n2, j2, h2, hy⟩ := cut_bind hy
      cases hy
      obtain ⟨rfl, rfl⟩ := word_at h1
      obtain ⟨rfl, rfl⟩ := word_at h2
      rfl
    · cases h
  · cases h

/-- The second word of the spelling of a binding tree's shape hangs on the number of bytes of a salt
alone. -/
theorem spellBinding_at (s : LinBindingShape) :
    wordAt (spellBinding s) (u64n 0).size = wordAt (u64n s.saltBytes) 0 := by
  have e : spellBinding s = u64n s.logLeaves ++ u64n s.saltBytes ++ ByteArray.empty := by
    simp [spellBinding, spellRow, spellWord, cat_cons, cat_nil]
  rw [e]
  exact wordAt_mid (u64n s.logLeaves) (u64n s.saltBytes) ByteArray.empty 0 (by
    rw [size_u64n])

/-! ## The two chains' parameter bytes -/

/-- The parameter bytes of the chains in what the planner returns are those that `configure` has
made. -/
theorem planned_made {pol KL : ByteArray} {layout : Option ByteArray} {p : Model.Verify.Planned}
    (h : Model.Verify.planned pol KL layout = .ok p) :
    ∃ l x bits, configure l x p.cfg bits = .ok p.chains.made := by
  unfold Model.Verify.planned at h
  obtain ⟨X, _, h⟩ := exc_bind h
  dsimp only at h
  obtain ⟨chains, hc, h⟩ := exc_bind h
  obtain ⟨_, _, h⟩ := exc_bind h
  cases h
  obtain ⟨shapes, hm⟩ := Model.Verify.chainsOf_made hc
  exact ⟨_, _, _, hm⟩

/-- The one-time chain's and the first chain's parameter bytes are spelled from plans at the setting
of the lines, and so are the two items "binding tree". -/
theorem configure_salts {l : Lines} {x : Shapes} {cfg : ByteArray} {bits : ℕ} {made : Configured}
    (h : configure l x cfg bits = .ok made) :
    ∃ P1 F : Planned,
      made.keyOneTime = paramsBytes P1.plan cfg (Plan.oneTimeItems made.sized.key) ∧
      made.first = paramsBytes F.plan cfg (madeFirstItems l x made.sized) ∧
      P1.set = settingOf l ∧ F.set = settingOf l ∧ made.sized.key.set = settingOf l ∧
      made.sized.set = settingOf l := by
  obtain ⟨P1, _, _, F, _, _, k1, f1, e1, -, -, -, e5, -, -⟩ := configure_bytes h
  obtain ⟨hz, -, Q1, _, _, k2, q1, -⟩ := configure_plans h
  obtain ⟨G, _, _, f2, g1, -⟩ := configure_proofPlans h
  obtain rfl : P1 = Q1 := by
    have := k1.symm.trans k2
    simp only [List.cons.injEq] at this
    exact this.1
  obtain rfl : F = G := by
    have := f1.symm.trans f2
    simp only [List.cons.injEq] at this
    exact this.1
  have sk : made.sized.key.set = settingOf l := (Plan.keySized_oneTime (sized_key hz)).2
  have sp : made.sized.proof.set = settingOf l := (proofSized_set (sized_proof hz)).1
  exact ⟨P1, F, e1, e5, (finishHeld_set q1).trans sk, (finishHeld_set g1).trans sp, sk,
    (sized_link hz).1⟩

section Planned
variable {pol KL : ByteArray} {layout : Option ByteArray} {p : Model.Verify.Planned}

/-- **One number of bytes of a salt** in the key's one-time chain and the proof's first chain. -/
theorem salt_one (h : Model.Verify.planned pol KL layout = .ok p)
    (hb1 : (p.chains.bytes .keyOneTime).size < 2 ^ 64)
    (hb3 : (p.chains.bytes .proofFirst).size < 2 ^ 64) :
    p.chains.key.oneTime.given.plan.salt = p.chains.proof.first.given.plan.salt := by
  have h32 := (Model.Verify.planned_spelled h).1
  obtain ⟨r1, -, r3⟩ := Model.Verify.planned_read h
  obtain ⟨l, x, bits, hm⟩ := planned_made h
  obtain ⟨P1, F, e1, e5, s1, s5, -, -⟩ := configure_salts hm
  have g1 := OneTime.read_given (KeyChains.read_parts r1).1
  have b1 : p.chains.bytes .keyOneTime = p.chains.made.keyOneTime := rfl
  rw [b1, e1] at g1 hb1
  have g3 := First.read_given (ProofChains.read_parts r3).1
  have b3 : p.chains.bytes .proofFirst = p.chains.made.first := rfl
  rw [b3, e5] at g3 hb3
  rw [given_salt hb1 h32 (oneTimeItems_names _) g1,
    given_salt hb3 h32 (madeFirstItems_names _ _ _) g3]
  show (UInt64.ofNat P1.set.saltBytes).toNat = (UInt64.ofNat F.set.saltBytes).toNat
  rw [s1, s5]

/-- **One number of bytes of a salt in the two binding trees.** -/
theorem bindingSalt_one (h : Model.Verify.planned pol KL layout = .ok p)
    (hb1 : (p.chains.bytes .keyOneTime).size < 2 ^ 64)
    (hb3 : (p.chains.bytes .proofFirst).size < 2 ^ 64) :
    p.chains.key.oneTime.binding.saltBytes = p.chains.proof.first.binding.saltBytes := by
  have h32 := (Model.Verify.planned_spelled h).1
  obtain ⟨K1, -, K3⟩ := TieK.planned_chains_open h
  obtain ⟨l, x, bits, hm⟩ := planned_made h
  obtain ⟨P1, F, e1, e5, -, -, sk, sz⟩ := configure_salts hm
  obtain ⟨_, _, t1, _, _, A⟩ := TieK.oneTime_read_open K1.oneTime
  obtain ⟨_, _, _, _, _, _, t3, B⟩ := TieK.first_read_open K3.first
  have g1 := A.given
  have b1 : p.chains.bytes .keyOneTime = p.chains.made.keyOneTime := rfl
  rw [b1, e1] at g1 hb1
  have i1 := (Given.read_items hb1 h32 (oneTimeItems_names _) g1).symm.trans A.items
  have g3 := B.given
  have b3 : p.chains.bytes .proofFirst = p.chains.made.first := rfl
  rw [b3, e5] at g3 hb3
  have i3 := (Given.read_items hb3 h32 (madeFirstItems_names _ _ _) g3).symm.trans B.items
  simp only [Plan.oneTimeItems, List.cons.injEq, Prod.mk.injEq, true_and] at i1
  simp only [madeFirstItems, madeLinItems, List.cons_append, List.nil_append, List.cons.injEq,
    Prod.mk.injEq, true_and] at i3
  rw [readBinding_salt A.binding, readBinding_salt B.binding, ← i1.2.2.1, ← i3.2.2.2.2.2.2.1,
    spellBinding_at, spellBinding_at]
  show (wordAt (u64n p.chains.made.sized.key.set.saltBytes) 0).toNat =
    (wordAt (u64n p.chains.made.sized.set.saltBytes) 0).toNat
  rw [sk, sz]

end Planned

/-- **Both, where the program has said yes.** -/
theorem salts_port {F : K.Files} {id : String} {table further : Params.TableName}
    (h : K.PortYesAt F id table further) {p : Model.Verify.Planned}
    (hp : Model.Verify.planned F.pol F.KL (some F.lay) = .ok p) :
    p.chains.key.oneTime.given.plan.salt = p.chains.proof.first.given.plan.salt ∧
      p.chains.key.oneTime.binding.saltBytes = p.chains.proof.first.binding.saltBytes := by
  obtain ⟨p₁, hp₁, hk⟩ := port_key_check h
  obtain ⟨p₂, _, _, _, _, hp₂, -, -, -, -, hc, -⟩ := TieK.port_common h
  obtain rfl : p₁ = p := Except.ok.inj (hp₁.symm.trans hp)
  obtain rfl : p₂ = p₁ := Except.ok.inj (hp₂.symm.trans hp)
  have b1 : (p₂.chains.bytes .keyOneTime).size < 2 ^ 64 :=
    Nat.lt_of_le_of_lt (Tie.key_yes_small hp hk) (by decide)
  have b3 : (p₂.chains.bytes .proofFirst).size < 2 ^ 64 :=
    Nat.lt_of_le_of_lt (Tie.proof_yes_small hp hc) (by decide)
  exact ⟨salt_one hp b1 b3, bindingSalt_one hp b1 b3⟩

end OnBytes.Maker.Page
