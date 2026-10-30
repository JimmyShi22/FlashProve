-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Tail/MeetLay.lean: the one ledger at a link's end, at the verifier's own exponents: a
value of the letter `lay` of `dig_know` (Cb/Pv/Tail/DigBatch.lean) at which its two premises on
`lay` hold under the condition that the link carries.

The ledger has two shares. The plain share holds the caller's claims, which stand in the statement,
and the lookup's end claims. Each has an exponent of its own below the plan's number of claims pc:
the list with these exponents is a letter `lo`. In the byte-level verifier the exponent of such a
claim is its number among the claims, and a caller's claims may stand in front of the lookup's and
behind them. The other share holds the single equations of the smallness test's ties and reads: the
verifier's own list with its own exponents, from pc on (`rowsForm`,
OnBytes/Tie/Pv/Tail/EndForms.lean), at the record of the statement
(OnBytes/Tie/Pv/Tail/MeetRows.lean). All are laid out in one ledger of n₃ places (`layout`,
Cb/Pv/Tail/Claims.lean).

Main names:
  `listP`: the two shares with their exponents. `layP`: the ledger.
  `length_layP`: it has n₃ claims, at every statement.
  `LoOK`: at a statement: the claims of `lo x'`, all holding, give every claim of the caller's
    ledger and every end claim of the lookup; no exponent stands twice; all are below pc.
  `loOK_numbered`: so for the caller's claims numbered from 0 on and the end claims numbered from a
    on, if the first are at most a and the second fit below pc.
  `exps_listP`: where `LoOK` holds: no exponent stands twice, and all are below n₃.
  `layR_of_listP`: the claims of the list, all holding, give `layR D (rowsAt ..)`.
  `hlay_layP`: at such a statement `layP` gives `layD`.
  `lay_paid`: the two premises of `dig_know` on `lay`, at `layP` and any condition P₃ behind the
    lookup that gives `LoOK`.

Limits: premises: those of `hrows_port`; at every statement: the record's shapes have as many rows
of symbols as their rows of cells want; pc and the number of the record's indices make n₃. That pc
and n₃ are a plan's numbers, and that `lo` has the verifier's exponents, is not said.

-/
import OnBytes.Tie.Pv.Tail.EndsThree
import OnBytes.Tie.Pv.Tail.MeetRows

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Tie.Pv.Tail
open OnBytes OnBytes.Model OnBytes.Road.Rows OnBytes.Tie.Pv.Tail.Port Cb.Pv.Tail

variable {K J : Type} [Field K] [Fintype J] (ρ : Reading K) (Y : Lay J) {t : TSize}
  {J₁ J₂ : Type} [Fintype J₁] [Fintype J₂] {Q : Host K t.size J₁ J₂}
  {U W₀ MM J₃ : Type} [Fintype J₃] [DecidableEq J₃] (T : LateU Q.let U W₀) (left : MM → Q.M)
  (right : MM → U) (D : Tail3 Q MM J₃) (rec : D.X' → HTailF2) (iJ : J → J₃)
  (lo : D.X' → List (ℕ × TWhole.Form K J₃)) (pc n₃ : ℕ)

/-- A list, numbered from c on. -/
def numbered {α : Type} (c : ℕ) (L : List α) : List (ℕ × α) := (List.range' c L.length).zip L

theorem snd_numbered {α : Type} (c : ℕ) (L : List α) : (numbered c L).map Prod.snd = L :=
  List.map_snd_zip (by rw [List.length_range'])

theorem mem_numbered {α : Type} (c : ℕ) {L : List α} {f : α} (h : f ∈ L) :
    ∃ z ∈ numbered c L, z.2 = f := by
  rw [← snd_numbered c L] at h
  obtain ⟨z, hz, e⟩ := List.mem_map.1 h
  exact ⟨z, hz, e⟩

/-- The plain share at a statement: its claims give the caller's ledger and the lookup's end claims;
no exponent twice; all below pc. -/
structure LoOK (x' : D.X') : Prop where
  gives : ∀ m, (∀ z ∈ lo x', z.2.Holds (D.msg₃ m)) →
    TWhole.Ledger.Holds ((D.pr x').1.2.map (pushF D.i12)) (D.msg₃ m) ∧
      TWhole.Ledger.Holds (D.endCl x') (D.msg₃ m)
  nodup : ((lo x').map Prod.fst).Nodup
  bound : ∀ z ∈ lo x', z.1 < pc

/-- The caller's claims numbered from 0 on, the end claims numbered from a on. -/
theorem loOK_numbered (a : ℕ) (x' : D.X') (hc : (D.pr x').1.2.length ≤ a)
    (he : a + (D.endCl x').length ≤ pc) :
    LoOK D (fun x' => numbered 0 ((D.pr x').1.2.map (pushF D.i12)) ++ numbered a (D.endCl x')) pc
      x' := by
  obtain ⟨n1, b1⟩ := exps_numbered 0 ((D.pr x').1.2.map (pushF D.i12))
  obtain ⟨n2, b2⟩ := exps_numbered a (D.endCl x')
  have c1 : ∀ z ∈ numbered 0 ((D.pr x').1.2.map (pushF D.i12)), z.1 < a := fun z hz => by
    have h := (b1 z hz).2
    rw [List.length_map, Nat.zero_add] at h
    exact lt_of_lt_of_le h hc
  refine ⟨fun m hm => ⟨fun f hf => ?_, fun f hf => ?_⟩, ?_, fun z hz => ?_⟩
  · obtain ⟨z, hz, e⟩ := mem_numbered 0 hf
    exact e ▸ hm z (List.mem_append_left _ hz)
  · obtain ⟨z, hz, e⟩ := mem_numbered a hf
    exact e ▸ hm z (List.mem_append_right _ hz)
  · rw [List.map_append, List.nodup_append]
    refine ⟨n1, n2, fun u hu v hv e => ?_⟩
    obtain ⟨z, hz, rfl⟩ := List.mem_map.1 hu
    obtain ⟨z', hz', rfl⟩ := List.mem_map.1 hv
    have := c1 z hz
    have := (b2 z' hz').1
    omega
  · rcases List.mem_append.1 hz with hz | hz
    · have := c1 z hz
      omega
    · exact lt_of_lt_of_le (b2 z hz).2 he

/-- The two shares with their exponents. -/
def listP (x' : D.X') : List (ℕ × TWhole.Form K J₃) :=
  lo x' ++ ([] ++ (rowsForm Y ρ (rec x') (rec x').funs pc).map fun p => (p.1, pushF iJ p.2))

/-- The one ledger, laid out by exponents. -/
def layP (x' : D.X') : TWhole.Ledger K J₃ := layout n₃ (listP ρ Y D rec iJ lo pc x')

omit [Fintype J₃] in
theorem length_layP (x' : D.X') : (layP ρ Y D rec iJ lo pc n₃ x').length = n₃ :=
  length_layout _ _

/-- Where the plain share is in order: no exponent twice, all below n₃. -/
theorem exps_listP (x' : D.X') (hk : LoOK D lo pc x')
    (hmS : ∀ mu, mu < (rec x').NM →
      ((rec x').shp.getD mu {}).mS = Alg.symRows ((rec x').shp.getD mu {}).m)
    (hn : pc + topOf (rec x') (rec x').funs = n₃) :
    ((listP ρ Y D rec iJ lo pc x').map Prod.fst).Nodup ∧
      ∀ z ∈ listP ρ Y D rec iJ lo pc x', z.1 < n₃ := by
  rw [← hn]
  exact exps_ledger Y (pushF iJ) ρ (rec x') (rec x').funs pc hmS hk.nodup List.nodup_nil hk.bound
    (fun z hz => absurd hz List.not_mem_nil) (le_refl pc)

/-- The claims of the list with exponents, all holding, give the ledger with the verifier's list. -/
theorem layR_of_listP (x' : D.X') (hk : LoOK D lo pc x') (m : MM)
    (h : ∀ z ∈ listP ρ Y D rec iJ lo pc x', z.2.Holds (D.msg₃ m)) :
    TWhole.Ledger.Holds (layR D (rowsAt ρ Y D rec iJ pc) x') (D.msg₃ m) := by
  obtain ⟨g1, g2⟩ := hk.gives m fun z hz => h z (List.mem_append_left _ hz)
  intro f hf
  rcases List.mem_append.1 hf with hf | hf
  · exact g1 f hf
  · rcases List.mem_append.1 hf with hf | hf
    · exact g2 f hf
    · unfold rowsAt rowsLedger at hf
      rw [List.map_map] at hf
      obtain ⟨p, hp, e⟩ := List.mem_map.1 hf
      exact e ▸ h (p.1, pushF iJ p.2) (List.mem_append_right _ (List.mem_append_right _
        (List.mem_map.2 ⟨p, hp, rfl⟩)))

variable {phi : Q.Xe → ℕ → ℕ → K} {symN : Q.M₁ → ℕ → ℕ → ℕ → K} {u3N : Q.U₁ → ℕ → K}

/-- Where the plain share is in order, the ledger gives the one ledger of
Cb/Pv/Tail/DigBatch.lean. -/
theorem hlay_layP (hT : IsT Q phi symN u3N) (ht : ∀ x', sizeOf (rec x') = t)
    (hs : ∀ m j, D.msg₃ m (D.is j) = vals Q.let (left m) (T.digs (right m)) j)
    (hAt : ∀ x' m, AtT ρ (rec x') t (thetaQ Q phi symN u3N) (D.pr x').1 (left m)
      (T.digs (right m)) (D.pr x').2 fun b r c => Y.cellAt (fun j => D.msg₃ m (iJ j)) b r c)
    (hfit : ∀ x', Fits (rec x')) (htree : ∀ x', ∀ Fn ∈ (rec x').funs.toList, Fn.tree = 2)
    (hmS : ∀ x' mu, mu < (rec x').NM →
      ((rec x').shp.getD mu {}).mS = Alg.symRows ((rec x').shp.getD mu {}).m)
    (hn : ∀ x', pc + topOf (rec x') (rec x').funs = n₃)
    (x' : D.X') (hk : LoOK D lo pc x') (m : MM)
    (h : TWhole.Ledger.Holds (layP ρ Y D rec iJ lo pc n₃ x') (D.msg₃ m)) :
    TWhole.Ledger.Holds (layD D x') (D.msg₃ m) := by
  obtain ⟨nd, lt⟩ := exps_listP ρ Y D rec iJ lo pc n₃ x' hk (hmS x') (hn x')
  exact hlay_rows T left right D (rowsAt ρ Y D rec iJ pc) hs
    (hrows_port ρ Y T left right D rec iJ pc hT ht hAt hfit htree) x' m
    (layR_of_listP ρ Y D rec iJ lo pc x' hk m
      ((layout_holds n₃ _ (D.msg₃ m) (inj_of_nodup nd) lt).1 h))

/-- The two premises of `dig_know` on the ledger that is laid, at `layP`, under any condition behind
the lookup that puts the plain share in order. -/
theorem lay_paid (hT : IsT Q phi symN u3N) (ht : ∀ x', sizeOf (rec x') = t)
    (hs : ∀ m j, D.msg₃ m (D.is j) = vals Q.let (left m) (T.digs (right m)) j)
    (hAt : ∀ x' m, AtT ρ (rec x') t (thetaQ Q phi symN u3N) (D.pr x').1 (left m)
      (T.digs (right m)) (D.pr x').2 fun b r c => Y.cellAt (fun j => D.msg₃ m (iJ j)) b r c)
    (hfit : ∀ x', Fits (rec x')) (htree : ∀ x', ∀ Fn ∈ (rec x').funs.toList, Fn.tree = 2)
    (hmS : ∀ x' mu, mu < (rec x').NM →
      ((rec x').shp.getD mu {}).mS = Alg.symRows ((rec x').shp.getD mu {}).m)
    (hn : ∀ x', pc + topOf (rec x') (rec x').funs = n₃)
    (P₃ : D.X' × Q.Ex.Str → Prop) (hP : ∀ x' y, P₃ (x', y) → LoOK D lo pc x') :
    (∀ x' y, P₃ (x', y) → (layP ρ Y D rec iJ lo pc n₃ x').length ≤ n₃) ∧
      ∀ x' y m, P₃ (x', y) →
        TWhole.Ledger.Holds (layP ρ Y D rec iJ lo pc n₃ x') (D.msg₃ m) →
          TWhole.Ledger.Holds (layD D x') (D.msg₃ m) :=
  ⟨fun x' _ _ => le_of_eq (length_layP ρ Y D rec iJ lo pc n₃ x'),
    fun x' y m hp h => hlay_layP ρ Y T left right D rec iJ lo pc n₃ hT ht hs hAt hfit htree hmS hn
      x' (hP x' y hp) m h⟩

end OnBytes.Tie.Pv.Tail

#print axioms OnBytes.Tie.Pv.Tail.loOK_numbered
#print axioms OnBytes.Tie.Pv.Tail.exps_listP
#print axioms OnBytes.Tie.Pv.Tail.layR_of_listP
#print axioms OnBytes.Tie.Pv.Tail.hlay_layP
#print axioms OnBytes.Tie.Pv.Tail.lay_paid
