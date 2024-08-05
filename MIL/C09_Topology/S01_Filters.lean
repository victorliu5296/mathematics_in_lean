import MIL.Common
import Mathlib.Topology.Instances.Real

open Set Filter Topology

def principal {α : Type*} (s : Set α) : Filter α
    where
  sets := { t | s ⊆ t }
  univ_sets := by simp only [mem_setOf_eq, subset_univ]
  sets_of_superset := fun a a_1 ⦃a_2⦄ a_3 ↦ a_1 (a a_3) -- by
    -- simp
    -- intro x y
    -- exact fun a a_1 ⦃a_2⦄ a_3 ↦ a_1 (a a_3)
  inter_sets := by
    simp
    exact fun {x y} a a_1 ↦ ⟨a, a_1⟩

example : Filter ℕ :=
  { sets := { s | ∃ a, ∀ b, a ≤ b → b ∈ s }
    univ_sets := by simp only [mem_setOf_eq, mem_univ, implies_true, exists_const]
    sets_of_superset := by
      simp
      exact fun {x y} x_1 h a ↦ Exists.intro x_1 fun b a_1 ↦ a (h b a_1)
    inter_sets := by
      intro x y hx hy
      simp
      exact exists_forall_ge_and hx hy
  }

#check 𝓝

def Tendsto₁ {X Y : Type*} (f : X → Y) (F : Filter X) (G : Filter Y) :=
  ∀ V ∈ G, f ⁻¹' V ∈ F

def Tendsto₂ {X Y : Type*} (f : X → Y) (F : Filter X) (G : Filter Y) :=
  map f F ≤ G

example {X Y : Type*} (f : X → Y) (F : Filter X) (G : Filter Y) :
    Tendsto₂ f F G ↔ Tendsto₁ f F G :=
  Iff.rfl

#check (@Filter.map_mono : ∀ {α β} {m : α → β}, Monotone (map m))

#check
  (@Filter.map_map :
    ∀ {α β γ} {f : Filter α} {m : α → β} {m' : β → γ}, map m' (map m f) = map (m' ∘ m) f)

example {X Y Z : Type*} {F : Filter X} {G : Filter Y} {H : Filter Z} {f : X → Y} {g : Y → Z}
    (hf : Tendsto₁ f F G) (hg : Tendsto₁ g G H) : Tendsto₁ (g ∘ f) F H := by
  unfold Tendsto₁
  intro V hV
  refine mem_map.mp ?_
  rw [← Filter.map_map]
  apply hf
  apply hg
  exact hV

variable (f : ℝ → ℝ) (x₀ y₀ : ℝ)

#check comap ((↑) : ℚ → ℝ) (𝓝 x₀)

#check Tendsto (f ∘ (↑)) (comap ((↑) : ℚ → ℝ) (𝓝 x₀)) (𝓝 y₀)

section
variable {α β γ : Type*} (F : Filter α) {m : γ → β} {n : β → α}

#check (comap_comap : comap m (comap n F) = comap (n ∘ m) F)

end

example : 𝓝 (x₀, y₀) = 𝓝 x₀ ×ˢ 𝓝 y₀ :=
  nhds_prod_eq

#check le_inf_iff

example (f : ℕ → ℝ × ℝ) (x₀ y₀ : ℝ) :
    Tendsto f atTop (𝓝 (x₀, y₀)) ↔
      Tendsto (Prod.fst ∘ f) atTop (𝓝 x₀) ∧ Tendsto (Prod.snd ∘ f) atTop (𝓝 y₀) := by
  unfold Tendsto
  have : 𝓝 (x₀) ×ˢ 𝓝 (y₀) = (comap Prod.fst (𝓝 (x₀)))
      ⊓ (comap Prod.snd (𝓝 (y₀))) := rfl
  constructor
  · intro h
    rw [nhds_prod_eq] at h
    rw [this, le_inf_iff] at h
    constructor <;> rw [← map_map]
    · refine map_le_iff_le_comap.mpr ?mp.left.a
      exact h.1
    · exact map_le_iff_le_comap.mpr h.2
  · rintro ⟨h₁, h₂⟩
    rw [nhds_prod_eq]
    rw [this, le_inf_iff]
    repeat' rw [← map_le_iff_le_comap, ← map_le_iff_le_comap, map_map]
    exact ⟨h₁, h₂⟩

example (x₀ : ℝ) : HasBasis (𝓝 x₀) (fun ε : ℝ ↦ 0 < ε) fun ε ↦ Ioo (x₀ - ε) (x₀ + ε) :=
  nhds_basis_Ioo_pos x₀

example (u : ℕ → ℝ) (x₀ : ℝ) :
    Tendsto u atTop (𝓝 x₀) ↔ ∀ ε > 0, ∃ N, ∀ n ≥ N, u n ∈ Ioo (x₀ - ε) (x₀ + ε) := by
  have : atTop.HasBasis (fun _ : ℕ ↦ True) Ici := atTop_basis
  rw [this.tendsto_iff (nhds_basis_Ioo_pos x₀)]
  simp

example (P Q : ℕ → Prop) (hP : ∀ᶠ n in atTop, P n) (hQ : ∀ᶠ n in atTop, Q n) :
    ∀ᶠ n in atTop, P n ∧ Q n :=
  hP.and hQ

example (u v : ℕ → ℝ) (h : ∀ᶠ n in atTop, u n = v n) (x₀ : ℝ) :
    Tendsto u atTop (𝓝 x₀) ↔ Tendsto v atTop (𝓝 x₀) :=
  tendsto_congr' h

example (u v : ℕ → ℝ) (h : u =ᶠ[atTop] v) (x₀ : ℝ) :
    Tendsto u atTop (𝓝 x₀) ↔ Tendsto v atTop (𝓝 x₀) :=
  tendsto_congr' h

#check eventually_of_forall
#check Eventually.mono
#check Eventually.and

example (P Q R : ℕ → Prop) (hP : ∀ᶠ n in atTop, P n) (hQ : ∀ᶠ n in atTop, Q n)
    (hR : ∀ᶠ n in atTop, P n ∧ Q n → R n) : ∀ᶠ n in atTop, R n := by
  apply (hP.and (hQ.and hR)).mono
  rintro n ⟨h, h', h''⟩
  exact h'' ⟨h, h'⟩

example (P Q R : ℕ → Prop) (hP : ∀ᶠ n in atTop, P n) (hQ : ∀ᶠ n in atTop, Q n)
    (hR : ∀ᶠ n in atTop, P n ∧ Q n → R n) : ∀ᶠ n in atTop, R n := by
  filter_upwards [hP, hQ, hR] with n h h' h'' using h'' ⟨h, h'⟩

#check mem_closure_iff_clusterPt
#check le_principal_iff
#check neBot_of_le

example (u : ℕ → ℝ) (M : Set ℝ) (x : ℝ) (hux : Tendsto u atTop (𝓝 x))
    (huM : ∀ᶠ n in atTop, u n ∈ M) : x ∈ closure M := by
  rw [mem_closure_iff_clusterPt]
  unfold ClusterPt
  have map_le_principal : map u atTop ≤ 𝓟 M := le_principal_iff.mpr huM
  have : map u atTop ≤ 𝓝 x ⊓ 𝓟 M :=
    Lattice.le_inf (map u atTop) (𝓝 x) (𝓟 M) hux map_le_principal
  exact neBot_of_le this
