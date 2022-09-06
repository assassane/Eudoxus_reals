import tactic.ring tactic.linarith tactic.omega data.set data.int.basic

local attribute [instance] classical.prop_decidable

def almost_homomorphism (f : ℤ → ℤ) : Prop :=
    ∃ C : ℤ, ∀ (p q : ℤ), abs (f (p + q) - f p - f q) < C

instance int_to_int.add_group : add_comm_group (ℤ → ℤ) :=
{ add := λ f g n,f n + g n,
  add_assoc := λ f g h,funext (λ n,add_assoc _ _ _),
  zero := λ n, 0,
  zero_add := λ f, funext (λ n,zero_add _),
  add_zero := λ f, funext (λ n,add_zero _),
  neg := λ f n,-f n,
  add_left_neg := λ f, funext (λ n, add_left_neg _),
  add_comm := λ f g, funext (λ n, add_comm _ _) }

@[simp]
lemma int_to_int_add (f g : ℤ → ℤ) (n : ℤ) : (f + g) n = f n + g n := rfl
@[simp]
lemma int_to_int_neg (f : ℤ → ℤ) (n : ℤ) : (-f) n = -f n := rfl
@[simp]
lemma int_to_int_zero : (0:ℤ → ℤ) = λ n, 0 := rfl

lemma almost_homomorphism_add {f g : ℤ → ℤ}
    (hf : almost_homomorphism f) (hg : almost_homomorphism g) :
    almost_homomorphism (f + g) :=
let ⟨Cf, hCf⟩:= hf in let ⟨Cg, hCg⟩ := hg in ⟨Cf+Cg,λ p q, calc
abs ((f + g) (p + q) - (f + g) p - (f + g) q) 
        = abs (f (p + q) + g (p + q) - (f p + g p) - (f q + g q)) : rfl
    ... = abs (f (p + q) - f p - f q + (g (p + q) - g p - g q)) : congr_arg abs (by ring)
    ... ≤ abs (f (p + q) - f p - f q) + abs (g (p + q) - g p - g q) : abs_add _ _
    ... < Cf + Cg : by linarith [hCf p q,hCg p q] ⟩

lemma almost_homomorphism_neg {f : ℤ → ℤ}
    (hf : almost_homomorphism f) :
    almost_homomorphism (-f) :=
let ⟨Cf,hCf⟩:=hf in ⟨Cf,λ p q, calc
abs ((-f) (p + q) - (-f) p - (-f) q) 
        = abs (-f (p + q) - -f p - -f q)  : rfl
    ... = abs (-(f (p + q) - f p - f q)) : by ring
    ... = abs (f (p + q) - f p - f q) : abs_neg _
    ... < Cf : hCf p q⟩

def bounded_difference (f g : ℤ → ℤ) : Prop := 
    ∃ C : ℤ, ∀ p : ℤ, abs (f p - g p) < C

lemma bounded_difference_add {f₁ g₁ f₂ g₂ : ℤ → ℤ}
    (hf : bounded_difference f₁ f₂) (hg : bounded_difference g₁ g₂) :
    bounded_difference (f₁ + g₁) (f₂ + g₂) :=
let ⟨Cf, hCf⟩:=hf in let ⟨Cg, hCg⟩:=hg in ⟨Cf + Cg,λ p,calc 
abs ((f₁ + g₁) p - (f₂ + g₂) p) 
        = abs ( f₁ p + g₁ p - (f₂ p + g₂ p)) : rfl
    ... = abs (f₁ p - f₂ p + (g₁ p - g₂ p)) : congr_arg abs (by ring)
    ... ≤ abs (f₁ p - f₂ p) + abs (g₁ p - g₂ p) : abs_add _ _
    ... < Cf + Cg : by linarith [hCf p,hCg p]⟩

lemma bounded_difference_neg {f₁ f₂ : ℤ → ℤ}
    (hf : bounded_difference f₁ f₂) :
    bounded_difference (-f₁) (-f₂) :=
let ⟨C,hC⟩:=hf in ⟨C, λ p, calc
abs ((-f₁) p - (-f₂) p) 
        = abs (-f₁ p - -f₂ p) : rfl
    ... = abs (- (f₁ p - f₂ p)) : by ring
    ... = abs (f₁ p - f₂ p) : abs_neg _
    ... < C : hC p⟩


structure S :=
(func : ℤ → ℤ) 
(AH : almost_homomorphism func)

lemma func_eq : ∀ {F G : S}, F.func = G.func → F = G
| ⟨f, _⟩ ⟨g, _⟩ rfl := rfl

lemma S_eq : ∀ {F G : S}, F = G → F.func = G.func := by tidy

instance : add_comm_group S := 
{ add := λ F G,⟨F.func + G.func,almost_homomorphism_add F.AH G.AH⟩,
  add_assoc := λ F G H, func_eq (add_assoc _ _ _),
  zero := ⟨0,⟨1,λ p q,by omega⟩⟩,
  zero_add := λ F, func_eq (zero_add _),
  add_zero := λ F, func_eq (add_zero _),
  neg := λ F,⟨-F.func,almost_homomorphism_neg F.AH⟩,
  add_left_neg := λ F, func_eq (add_left_neg _),
  add_comm := λ F G, func_eq (add_comm _ _) }

@[simp]
lemma zero_S_func_eq : (0:S).func = (0:ℤ → ℤ) := rfl 

@[simp]
lemma neg_S_func_eq (T : S) : (-T).func = -(T.func) := rfl

instance S.equiv : setoid S := { r := λ F G,bounded_difference F.func G.func,
  iseqv := 
  ⟨λ F ,⟨1,by norm_num⟩,
  λ F G h ,let ⟨C,hC⟩:= h  in ⟨C,by simp [abs_sub];exact hC⟩,
  λ F G H hFG hGH ,let ⟨C_FG,hCFH⟩:=hFG in let ⟨C_GH,hCGH⟩:= hGH in
  ⟨C_FG+C_GH, λ p, calc 
  abs (F.func p - H.func p) 
        = abs (F.func p - G.func p + (G.func p - H.func p)) : by ring
    ... ≤ abs (F.func p - G.func p) + abs (G.func p - H.func p) : abs_add _ _
    ... < C_FG + C_GH : by linarith [hCFH p, hCGH p]⟩⟩ }

def E := @quotient S S.equiv

def mk : S → E := quotient.mk 

@[simp] 
lemma mk_eq_mk (F) :  ⟦F⟧ = (mk F) := rfl

@[simp]
lemma mk_eq {F G} : mk F = mk G ↔ F ≈ G := quotient.eq

@[simp]
lemma mk_eq_mk' (f : S) : quot.mk setoid.r f = mk f := rfl

instance : has_zero E := ⟨mk 0⟩ 

@[simp] lemma zero_def : 0 = mk 0 := rfl

instance : has_add E := 
⟨λ x y,quotient.lift_on₂ x y (λ F G, mk (F + G)) $
    λ F₁ G₁ F₂ G₂ hF hG, quotient.sound $
    bounded_difference_add hF hG⟩

@[simp] theorem mk_add (F G : S) : mk F + mk G = mk (F + G) := rfl

instance : has_neg E :=
⟨λ x, quotient.lift_on x (λ F, mk (-F)) $
  λ F₁ F₂ hF, quotient.sound $
  bounded_difference_neg hF⟩

@[simp] theorem mk_neg (F : S) : -mk F = mk (-F) := rfl

instance : add_comm_group E :=
{ add := (+),
  add_assoc := by repeat {refine λ a, quotient.induction_on a (λ _, _)};simp [add_assoc],
  zero := 0,
  zero_add := by repeat {refine λ a, quotient.induction_on a (λ _, _)};simp,
  add_zero := by repeat {refine λ a, quotient.induction_on a (λ _, _)};simp,
  neg := λ x,-x,
  add_left_neg := by repeat {refine λ a, quotient.induction_on a (λ _, _)};simp,
  add_comm := by repeat {refine λ a, quotient.induction_on a (λ _, _)};simp [add_comm] }


def int_to_int.mapping : ℤ → (ℤ → ℤ) := λ A,λ p, A*p
def S.mapping : ℤ → S := λ A,⟨λ p, A*p,⟨1,λ q r,by simp [left_distrib];norm_num⟩⟩
def E.mapping : ℤ → E := λ A,mk ⟨λ p, A*p,⟨1,λ q r,by simp [left_distrib];norm_num⟩⟩

lemma nat.rec_on_sup
{C : ℕ → Prop} (n i : ℕ) (hp : n ≥ i) (hi : C i)
(hr : ∀ (n : ℕ), C n → C (nat.succ n)) : C n :=
begin
  cases (nat.eq_or_lt_of_le hp).symm,
    {induction h with k hle ht,
      {exact hr i hi},
      replace hle : i + 1 ≤ k := hle,
      refine hr k (ht $ le_trans (nat.le_succ i) hle)},
    rwa ←h
end


lemma lemma3 (f : ℤ → ℤ) (hf : almost_homomorphism f) 
    (hfi : set.infinite ((f ''{n | n > 0}) ∩ {n | n>0})) : ∀ D>0,∃ M>0,∀ m>0, f (m*M) > (m+1)*D :=
begin

intros D hD,
cases hf with C hC,
set E:=C+D with HE,
have h₁ : ∃ M>0, f M > 2*E,
{   begin
        by_contra hh, simp at hh,
        apply hfi,
        have h₂ : f '' {n | n > 0} ∩ {n | n>0} ⊆ { n | n ≤ 2*E ∧ n≥0}, 
            from λ n hn,let ⟨x,hx,hx'⟩:=(set.mem_image _ _ _).1 hn.1 in 
            ⟨hx' ▸ hh x hx,le_of_lt hn.2⟩,
        apply set.finite.subset _ h₂,
        have h₃ : { n : ℤ | n ≤ 2*E ∧ n≥0} ⊆ coe ''{n : ℕ | ↑n ≤ 2*E},
            from λ n hn,let ⟨n',hn'⟩:=int.eq_coe_of_zero_le hn.2 in
            (set.mem_image _ _ _).2 ⟨n',⟨by simpa [hn'] using hn.1,hn'.symm⟩⟩,
        apply set.finite.subset _ h₃,
        apply set.finite.image,
        cases lt_or_ge E 0 with hE hE,
        {   have h₄ : {n : ℕ | ↑n ≤ 2 * E}=∅,
            {   apply set.eq_empty_iff_forall_not_mem.2,
                intro x, simp,linarith},
            rw h₄, exact set.finite_empty },
        cases int.eq_coe_of_zero_le hE with  E' hE',
        have h₄ : {n : ℕ | ↑n ≤ 2 * E} = {n : ℕ | n ≤ 2*E'},
        {   simp [hE',int.coe_nat_le.symm]},
        rw h₄, exact set.finite_le_nat _
    end},
have h₂ : C>0,from lt_of_le_of_lt (abs_nonneg _) (hC 0 0),
rcases h₁ with ⟨M,hM,hM'⟩,
use M, use hM,
intros m hm,
have h₃ : f (m * M) > (m + 1) * E,
{   rcases int.eq_coe_of_zero_le (le_of_lt hm) with ⟨m',hhm'⟩,
    rw hhm' at *,
    apply nat.rec_on_sup m' 1 (int.coe_nat_pos.mp hm),
    {  calc 
        f (↑1 * M) 
                = f M : by simp
            ... > 2*E : hM' },
    {   intros m hm',
        calc f (↑(m.succ) * M) 
                = f ( (↑m+1)*M) : rfl
            ... = f ( ↑m * M + M) : by ring
            ... = f (↑m * M) + f M + ( f ( ↑m * M + M) - f (↑m * M) - f M ) : by ring
            ... > f (↑m * M) + f M - C : add_lt_add_left (abs_lt.1 (hC _ _)).1 _
            ... > f (↑m * M) + f M - E : add_lt_add_left (neg_lt_neg ((lt_add_iff_pos_right _).2 hD)) _
            ... = f (↑m * M) + (f M - E) :  add_assoc _ _ _
            ... > (↑m + 1) * E + (f M - E) : add_lt_add_right hm' _ 
            ... = f M + ((↑m + 1) * E - E) : by ring
            ... > 2 * E + ((↑m + 1) * E - E) : add_lt_add_right hM' _
            ... = (↑m + 2) * E : by ring
            ... = ((↑m+1) +1)*E : by ring
            ... = (↑(m+1) +1)*E : by simp
            ... = (↑(m.succ) + 1) * E : by ring }
},
calc 
f (m * M) 
        > (m + 1) * E : h₃
    ... = (m + 1) * C + (m + 1) * D : by ring
    ... > (m + 1) * D : (lt_add_iff_pos_left _).2 (mul_pos (by linarith) h₂)

end

lemma finite.exists_max {α : Type*} [linear_order α] (s : set α) (h : set.finite s) :
    s.nonempty → ∃ x∈s, ∀ y∈s, x ≥ y :=
set.exists_max_image s id h

lemma finite.exists_min {α : Type*} [linear_order α] (s : set α) (h : set.finite s) :
    s.nonempty → ∃ x∈s, ∀ y∈s, x ≤ y :=
set.exists_min_image s id h


lemma infinite_or (f : ℤ → ℤ) : 
      set.infinite ((f ''{n | n > 0}) ∩ {n | n>0})
    ∨ set.infinite ((f ''{n | n > 0}) ∩ {n | n<0})
    ∨ (∃ C,∀ n>0,abs (f n) ≤ C) :=
begin
by_contra H,
simp [decidable.not_or_iff_and_not]at H,
simp [set.infinite,not_not] at H,
have h : set.finite  (f ''{n | n > 0}),
{   have h':=set.finite.union H.1 H.2.1,
    simp [set.inter_union_distrib_left.symm] at h',
    have hh':{n : ℤ | n>0} ∪ {n | n<0} =  {n : ℤ | ¬n = 0},
    {   ext1,split;intros,
        {   exact or.elim a (λ ha,ne_of_gt ha) (λ ha,ne_of_lt ha)},
        {   exact or.symm (lt_or_gt_of_ne a)}},
    rw hh' at h',
    have h'':=
        set.finite.union h' (set.finite.subset (set.finite_singleton 0) (set.inter_subset_right (f ''{n | n > 0}) _)),
    simp only [set.inter_union_distrib_left.symm] at h'',
    have hh'':{n : ℤ | ¬n = 0} ∪ {0} = set.univ,
    {   ext1,split;intros,
        {   exact set.mem_univ _},
        {   exact or.symm (decidable.em (x=0))}},
    simp [hh''] at h'',
    exact h''
},
rcases finite.exists_max _ h ⟨f 1,(set.mem_image _ _ _).2 ⟨1,⟨by norm_num,rfl⟩⟩⟩ 
    with ⟨x,hx,hx'⟩,
rcases finite.exists_min _ h ⟨f 1,(set.mem_image _ _ _).2 ⟨1,⟨by norm_num,rfl⟩⟩⟩ 
    with ⟨xx,hhx,hhx'⟩,
by_cases hhxx : x ≥ -xx,
{   rcases H.2.2 (x) with ⟨y,hy⟩,
    have hhh:=hx' (f y) ((set.mem_image _ _ _).2 ⟨y,hy.1,rfl⟩),
    have hhh':=hhx' (f y) ((set.mem_image _ _ _).2 ⟨y,hy.1,rfl⟩),
    cases (lt_max_iff.1 hy.2) with hhy hhy,
    {   linarith},
    {   linarith}
},
{
    rcases H.2.2 (-xx) with ⟨y,hy⟩,
    have hhh:=hx' (f y) ((set.mem_image _ _ _).2 ⟨y,hy.1,rfl⟩),
    have hhh':=hhx' (f y) ((set.mem_image _ _ _).2 ⟨y,hy.1,rfl⟩),
    cases (lt_max_iff.1 hy.2) with hhy hhy,
    {   linarith},
    {   linarith}
}
end

lemma bounded_lt_of_le (f : ℤ → ℤ) : 
    (∃ C,∀ n>0,abs (f n) ≤ C) → (∃ C,∀ n>0,abs (f n) < C) :=
λ h,let ⟨C,hC⟩:= h in ⟨C+1,λ n hn,by linarith [hC n hn]⟩

lemma exists_max_of_ico (f : ℤ → ℤ) (a b : ℤ) (hab : a > b) :
    ∃ E,∀ r, b ≤ r → r < a → E > abs (f r) :=
begin
    have hf : set.finite (set.Ico b a),
        {   refine int.induction_on' b a _ _ _,
            {   simp},
            {   intros k hk hk',
                apply set.finite.subset hk',
                intros r hr, simp at *, linarith
            },
            {   intros k hk hk',
                convert set.finite.insert (k - 1) hk',
                ext1;intros,split;intros,
                {   cases eq_or_lt_of_le a_1.1 with hh hh,
                    {   exact or.inl hh.symm},
                    {   exact or.inr ⟨by linarith,a_1.2⟩}},
                {   cases a_1 with hh hh,
                    {   simp [hh],linarith},
                    {   exact ⟨by linarith [hh.1],hh.2⟩}
                } 
            }
        },
    rcases set.exists_max_image (set.Ico b a) f hf ⟨b,set.left_mem_Ico.mpr hab⟩ with ⟨E,hE,hE'⟩,
    rcases set.exists_min_image (set.Ico b a) f hf ⟨b,set.left_mem_Ico.mpr hab⟩ with ⟨F,hF,hF'⟩,
    by_cases H : f E>-f F,
    {   use (f E) + 1, intros r hrb hra,
        have hhE:= hE' r ⟨hrb,hra⟩,
        have hhF:= hF' r ⟨hrb,hra⟩, simp [abs_lt],
        split;linarith
    },
    {   use (-f F) + 1, intros r hrb hra,
        have hhE:= hE' r ⟨hrb,hra⟩,
        have hhF:= hF' r ⟨hrb,hra⟩, simp [abs_lt] at *,
        exact ⟨by linarith,by linarith⟩
    }
end

lemma lemma5_aux (f : ℤ → ℤ) (hf : almost_homomorphism f)
    (h : (f '' {n : ℤ | n > 0} ∩ {n : ℤ | n > 0}).infinite) :
    (∀ C>0,∃ N>0,∀ p>N, f p > C) :=
begin
    intros C hC,
    rcases hf with ⟨D,hD⟩,
    have hl := lemma3 f ⟨D,hD⟩ h D (lt_of_le_of_lt (abs_nonneg _) (hD 0 0)),
    rcases hl with ⟨M,hM,hM'⟩,
    set g:=λ p:ℤ,f (( p / M : ℤ ) * M) with hg,
    rcases exists_max_of_ico f M 0 hM with ⟨E,hE⟩,
    have hh: ∀ p:ℤ,abs ((f-g) p) < E+D,from λ p, 
        have h₁ : p = p/M * M + p%M,by simp [int.mod_def];ring,
        have h₂ : g (p/M * M + p%M) = f (p/M * M),by rw [←h₁],
        calc
        abs ((f-g) p)
                = abs ((f-g) (p/M * M + p%M)) : congr_arg (abs) (congr_arg (f-g) h₁)
            ... = abs (f (p/M * M + p%M) - g (p/M * M + p%M)) : rfl
            ... = abs ( f (p/M * M) + f (p%M) + (f (p/M * M + p%M) - f (p/M * M) - f (p%M)) - f (p/M * M)) 
                    : by rw [h₂];exact congr_arg abs (by ring)
            ... = abs ( f (p%M) + (f (p/M * M + p%M) - f (p/M * M) - f (p%M))) : congr_arg abs (by ring)
            ... ≤ abs ( f (p%M) ) + abs (f (p/M * M + p%M) - f (p/M * M) - f (p%M)) : abs_add _ _
            ... < E + D : add_lt_add 
                            (hE _ (int.mod_nonneg _ (ne_of_gt hM)) (int.mod_lt_of_pos p hM))
                            (hD _ _),
    have h₃ : ∃ n>0, (n+1)*D > (E + D) + C,from
    ⟨((E + D) + C)/D + 1,add_pos_of_nonneg_of_pos (int.div_nonneg 
    (le_of_lt (by linarith [lt_of_le_of_lt (abs_nonneg _) (hD 1 1),lt_of_le_of_lt (abs_nonneg _) (hE 0 (le_refl _) hM)]))
    (le_trans (abs_nonneg _) (le_of_lt (hD 1 1)))) (by norm_num),
    have h':(E + D + C) / D + 1 + 1> (E + D + C) / D,by linarith,
    int.lt_mul_of_div_lt (by linarith [lt_of_le_of_lt (abs_nonneg _) (hD 1 1),lt_of_le_of_lt (abs_nonneg _) (hE 0 (le_refl _) hM)]) h'⟩,
    rcases h₃ with ⟨n,hn,hn'⟩,
    set N:=n*M with hN,
    use N, split, {exact mul_pos hn hM}, intros p hp,
    have h₁ : p = p/M * M + p%M,by simp [int.mod_def];ring,
    have h₂ : g (p/M * M + p%M) = f (p/M * M),by rw [←h₁],
    have h₄ : p/M ≥ n,
    {   rw [hN] at hp,
        exact (int.le_div_iff_mul_le hM).2 (le_of_lt hp)},
    have h₅ : g p > (E + D) + C, from calc
        g p = f (p/M * M) : by rw [←h₂,←h₁]
        ... > (p/M +1) * D : hM' _ (gt_of_ge_of_gt h₄ hn)
        ... ≥ (n + 1) * D : (mul_le_mul_right (lt_of_le_of_lt (abs_nonneg (f (0 + 0) - f 0 - f 0)) (hD 0 0))).2 (add_le_add_right h₄ _)
        ... > (E + D) + C : hn',
    exact calc f p > g p - (E + D) : lt_sub_iff_add_lt'.mp (abs_lt.1 (hh p)).1
         ... > C : lt_sub_iff_add_lt'.mpr h₅
end

lemma lemma5_aux' (f : ℤ → ℤ) (hf : almost_homomorphism f)
    (h : (f '' {n : ℤ | n > 0} ∩ {n : ℤ | n > 0}).infinite) :
    (∀ C≥0,∃ N>0,∀ p≥N, f p ≥ C) :=
begin
    intros C hC,
    rcases hf with ⟨D,hD⟩,
    have hl := lemma3 f ⟨D,hD⟩ h D (lt_of_le_of_lt (abs_nonneg _) (hD 0 0)),
    rcases hl with ⟨M,hM,hM'⟩,
    set g:=λ p:ℤ,f (( p / M : ℤ ) * M) with hg,
    rcases exists_max_of_ico f M 0 hM with ⟨E,hE⟩,
    have hh: ∀ p:ℤ,abs ((f-g) p) < E+D,from λ p, 
        have h₁ : p = p/M * M + p%M,by simp [int.mod_def];ring,
        have h₂ : g (p/M * M + p%M) = f (p/M * M),by rw [←h₁],
        calc
        abs ((f-g) p)
                = abs ((f-g) (p/M * M + p%M)) : congr_arg (abs) (congr_arg (f-g) h₁)
            ... = abs (f (p/M * M + p%M) - g (p/M * M + p%M)) : rfl
            ... = abs ( f (p/M * M) + f (p%M) + (f (p/M * M + p%M) - f (p/M * M) - f (p%M)) - f (p/M * M)) 
                    : by rw [h₂];exact congr_arg abs (by ring)
            ... = abs ( f (p%M) + (f (p/M * M + p%M) - f (p/M * M) - f (p%M))) : congr_arg abs (by ring)
            ... ≤ abs ( f (p%M) ) + abs (f (p/M * M + p%M) - f (p/M * M) - f (p%M)) : abs_add _ _
            ... < E + D : add_lt_add 
                            (hE _ (int.mod_nonneg _ (ne_of_gt hM)) (int.mod_lt_of_pos p hM))
                            (hD _ _),
    have h₃ : ∃ n>0, (n+1)*D > (E + D) + C,from
    ⟨((E + D) + C)/D + 1,add_pos_of_nonneg_of_pos (int.div_nonneg 
    (le_of_lt (by linarith [lt_of_le_of_lt (abs_nonneg _) (hD 1 1),lt_of_le_of_lt (abs_nonneg _) (hE 0 (le_refl _) hM)]))
    (le_trans (abs_nonneg _) (le_of_lt (hD 1 1)))) (by norm_num),
    have h':(E + D + C) / D + 1 + 1> (E + D + C) / D,by linarith,
    int.lt_mul_of_div_lt (by linarith [lt_of_le_of_lt (abs_nonneg _) (hD 1 1),lt_of_le_of_lt (abs_nonneg _) (hE 0 (le_refl _) hM)]) h'⟩,
    rcases h₃ with ⟨n,hn,hn'⟩,
    set N:=n*M with hN,
    use N,split,{exact mul_pos hn hM}, intros p hp,
    have h₁ : p = p/M * M + p%M,by simp [int.mod_def];ring,
    have h₂ : g (p/M * M + p%M) = f (p/M * M),by rw [←h₁],
    have h₄ : p/M ≥ n,
    {   rw [hN] at hp,
        exact (int.le_div_iff_mul_le hM).2 hp},
    have h₅ : g p > (E + D) + C, from calc
        g p = f (p/M * M) : by rw [←h₂,←h₁]
        ... > (p/M +1) * D : hM' _ (gt_of_ge_of_gt h₄ hn)
        ... ≥ (n + 1) * D : (mul_le_mul_right (lt_of_le_of_lt (abs_nonneg (f (0 + 0) - f 0 - f 0)) (hD 0 0))).2 (add_le_add_right h₄ _)
        ... > (E + D) + C : hn',
    exact calc f p ≥ g p - (E + D) : le_of_lt (lt_sub_iff_add_lt'.mp (abs_lt.1 (hh p)).1)
         ... ≥ C : le_of_lt (lt_sub_iff_add_lt'.mpr h₅)
end

lemma lemma5_neg_aux (f : ℤ → ℤ) (hf : almost_homomorphism f)
    (h : set.infinite ((f ''{n | n > 0}) ∩ {n | n<0})) :
    (∀ C>0,∃ N>0,∀ p>N, f p < -C) :=
begin
    have := lemma5_aux (-f) (almost_homomorphism_neg hf) _,
    {   simp only [lt_neg];exact this},
    {   intro hh,
        apply h,
        have h₁ : {n : ℤ | n > 0} = (λ x,-x) ''{n : ℤ | n < 0},
        {   ext1;intros,split;intros,
            {   apply (set.mem_image _ _ _).2,
                use (-x),exact ⟨set.mem_def.2 (neg_lt_zero.2 a),neg_neg x⟩},
            {   rcases (set.mem_image _ _ _).1 a with ⟨y,hy,hy'⟩,
                rw ←hy', exact set.mem_def.2 (neg_pos.2 hy)}},
        have h₂ : (-f) '' {n : ℤ | n > 0} = (λ x,-x) '' (f ''{n : ℤ | n > 0}),
        {   ext1;intros,split;intros,
            {   apply (set.mem_image _ _ _).2,
                apply (set.mem_image _ _ _).2,
                rcases (set.mem_image _ _ _).1 a with ⟨y,hy,hy'⟩,
                rw ←hy',
                use (f y),
                exact ⟨(set.mem_image _ _ _).2 ⟨y,hy,rfl⟩,rfl⟩
                },
            {   apply (set.mem_image _ _ _).2,
                rcases (set.mem_image _ _ _).1 a with ⟨y,hy,hy'⟩,
                rcases (set.mem_image _ _ _).1 hy with ⟨z,hz,hz'⟩,
                rw [←hy',←hz'] at *,
                use z, exact ⟨hz,rfl⟩
            }},
        have h₃ : (-f) '' {n : ℤ | n > 0} ∩ {n : ℤ | n > 0} = (λ x,-x) '' (f '' {n : ℤ | n > 0} ∩ {n : ℤ | n < 0}),
        {   rw [←set.image_inter neg_injective,←h₁,←h₂]},
        rw h₃ at hh,
        apply (@set.finite_image_iff _ _ _ has_neg.neg _).1 hh,
        apply set.inj_on.mono (set.subset_univ _),
        exact set.injective_iff_inj_on_univ.1 neg_injective
    }
end

lemma lemma5_not_i_of_ii (f : ℤ → ℤ) : 
    (∀ C>0,∃ N,∀ p>N, f p > C) → ¬(∃ C, ∀ p, abs (f p) < C) :=
begin
    intros h hn,
    rcases hn with ⟨C,hC⟩,
    rcases h C (lt_of_le_of_lt (abs_nonneg _) (hC 0)) with ⟨N,hN⟩,
    have h₁ := (abs_lt.1 (hC (N+1))).2,
    have h₂ := hN (N+1) (by linarith),
    linarith
end

lemma lemma5_not_iii_of_i (f : ℤ → ℤ) : 
    (∃ C, ∀ p, abs (f p) < C) → ¬(∀ C>0,∃ N,∀ p>N, f p < -C) :=
begin
    intros h hn,
    rcases h with ⟨C,hC⟩,
    rcases hn C (lt_of_le_of_lt (abs_nonneg _) (hC 0)) with ⟨N,hN⟩,
    have h₁ := (abs_lt.1 (hC (N+1))).1,
    have h₂ := hN (N+1) (lt_add_one _),
    linarith
end

lemma lemma5_not_iii_of_ii (f : ℤ → ℤ) :
    (∀ C>0,∃ N>0,∀ p>N, f p > C) → ¬(∀ C>0,∃ N>0,∀ p>N, f p < -C) :=
begin
    intros h hn,
    rcases h 1 (by linarith) with ⟨N,hN,hN'⟩,
    rcases hn 1 (by linarith) with ⟨M,hM,hM'⟩,
    have h₁ := hN' (max (N+1) (M+1)) (lt_max_iff.2 (or.inl (lt_add_one N))),
    have h₂ := hM' (max (N+1) (M+1)) (lt_max_iff.2 (or.inr (lt_add_one M))),
    linarith
end

lemma lemma5_not_ii_of_iii (f : ℤ → ℤ) :
    (∀ C>0,∃ N>0,∀ p>N, f p < -C) → ¬(∀ C>0,∃ N>0,∀ p>N, f p > C) :=
begin
    intros h hn,
    rcases h 1 (by linarith) with ⟨N,hN,hN'⟩,
    rcases hn 1 (by linarith) with ⟨M,hM,hM'⟩,
    have h₁ := hN' (max (N+1) (M+1)) (lt_max_iff.2 (or.inl (lt_add_one N))),
    have h₂ := hM' (max (N+1) (M+1)) (lt_max_iff.2 (or.inr (lt_add_one M))),
    linarith
end

lemma lemma5_aux_iff (f : ℤ → ℤ) (hf : almost_homomorphism f) :
    set.infinite ((f ''{n | n > 0}) ∩ {n | n>0}) ↔ (∀ C>0,∃ N>0,∀ p>N, f p > C) :=
⟨λ h,lemma5_aux f hf h,λ h hn,
    begin
        replace hn : ¬(f '' {n : ℤ | n > 0} ∩ {n : ℤ | n > 0}).infinite,
        {   simp [set.infinite,not_not],exact hn},
        have h₁ := or.resolve_left (infinite_or f) hn,
        cases h₁ with h' h',
        {   have h₂ := lemma5_neg_aux f hf h',
            exact lemma5_not_iii_of_ii f h h₂},
        {   replace h':=bounded_lt_of_le f h',
            rcases h' with ⟨C,hC⟩,
            rcases h C (lt_of_le_of_lt (abs_nonneg _) (hC 1 (by linarith))) with ⟨N,hN,hN'⟩,
            have h₂ := hN' (max (N+1) 1) (lt_max_iff.2 (or.inl (lt_add_one N))),
            have h₃ := (abs_lt.1 (hC (max (N+1) 1) (lt_max_iff.2 (or.inr (int.one_pos))))).2,
            linarith }
    end⟩


lemma lemma5 (f : ℤ → ℤ) (hf : almost_homomorphism f) :
      (∃ C, ∀ p, abs (f p) < C) 
    ∨ (∀ C>0,∃ N>0,∀ p>N, f p > C)
    ∨ (∀ C>0,∃ N>0,∀ p>N, f p < -C):=
begin
cases infinite_or f with h h',
{   
    apply or.inr, apply or.inl,
    exact lemma5_aux f hf h
}, 
{   cases h' with h h,
{   apply or.inr, apply or.inr,
    exact lemma5_neg_aux f hf h
},

{   apply or.inl,
    rcases bounded_lt_of_le f h with ⟨C,hC⟩,
    rcases hf with ⟨D,hD⟩,
    use (C+D+abs (f 0)), intro p,
    cases lt_trichotomy 0 p with hp hp',
    {   linarith [hC p hp,abs_nonneg (f 0),lt_of_le_of_lt (abs_nonneg _) (hD 1 1)]},
    cases hp' with hp hp,
    {   rw [←hp],linarith [lt_of_le_of_lt (abs_nonneg _) (hD 1 1),lt_of_le_of_lt (abs_nonneg _) (hC 1 (by norm_num))]},
    {   have h₁ : f p = f 0 - f (-p) - (f (p + (-p)) - f p - f (-p)),
        {   simp,ring},
        have h₂ : abs (f (p + -p) - f p - f (-p)) < D,from hD _ _,
        have h₃ : abs (f (-p)) < C,from hC _ (by linarith),
        calc abs (f p) 
                = abs (f 0 + -f (-p) + -(f (p + (-p)) - f p - f (-p))) : congr_arg _ h₁
            ... ≤ abs (f 0) + abs (-f (-p)) + abs (-(f (p + (-p)) - f p - f (-p))) : abs_add_three _ _ _
            ... = abs (f 0) + abs (f (-p)) + abs (f (p + (-p)) - f p - f (-p)) : by rw [abs_neg,abs_neg]
            ... < C + D + abs (f 0) : by linarith
}}},

end

class pos_add_comm_group (α : Type*) extends add_comm_group α :=
(pos : α → Prop)
(zero_nonpos : ¬ pos 0)
(add_pos : ∀ {x y}, pos x → pos y → pos (x + y))
(pos_antisymm : ∀ {x}, (pos x ↔ pos (-x)) → x = 0) -- if x≠0, then either x or -x is positive

section

open pos_add_comm_group

instance pos_add_comm_group.to_nonneg_add_comm_group (α : Type*) [s : pos_add_comm_group α] : 
 nonneg_add_comm_group α := 
{ 
  nonneg := λ x,¬ pos (-x),
  pos := pos,
  pos_iff := λ x,⟨λ h,⟨or.elim (classical.em (x = 0)) (λ hx,false.elim (zero_nonpos (by rwa hx at h))) 
    (λ hx hn,hx (pos_antisymm (iff_of_true h hn))),
    by simp;exact h⟩,λ h,by simp at h;exact h.2⟩,
  zero_nonneg := by simp;exact zero_nonpos,
  add_nonneg := λ x y hx hy hn,
  begin
    by_cases hx':x=0,
    {   simp [hx'] at hn,
        apply hy hn},
    {   by_cases hy':y=0,
        {   simp [hy'] at hn,
        apply hx hn},
        {   have h₁ : ∀ {p q : Prop},¬(p↔q) → (p ∧ ¬q) ∨ (¬p ∧ q),tauto,
            have hhx:= h₁ ((mt pos_antisymm) hx'),
            have hhy:= h₁ ((mt pos_antisymm) hy'),
            cases hhx with hhx' hhx',
            {   cases hhy with hhy' hhy',
                {   have h₂ := add_pos hhx'.1 hhy'.1,
                    have h₃ := add_pos h₂ hn,
                    rw [←sub_eq_add_neg,sub_self] at h₃ ,
                    exact zero_nonpos h₃ },
                {   exact hy hhy'.2}},
            {   exact hx hhx'.2}}},
  end,
  nonneg_antisymm := λ x h hh,
  begin
    rw [neg_neg] at hh,
    exact pos_antisymm (iff_of_false hh h)
  end,
  ..s }

end


lemma iff_infinite_pos_of_pos_of_bounded_difference (f g : ℤ → ℤ) 
    (hf : almost_homomorphism f) (hg : almost_homomorphism g) (h : bounded_difference f g): 
    (f '' {n : ℤ | n > 0} ∩ {n : ℤ | n > 0}).infinite ↔
    (g '' {n : ℤ | n > 0} ∩ {n : ℤ | n > 0}).infinite :=
begin
rcases h with ⟨C,hC⟩,
simp [lemma5_aux_iff f hf,lemma5_aux_iff g hg],
split,
{   intros hh D hD,
    rcases hh (D+C) (add_pos hD (lt_of_le_of_lt (abs_nonneg _) (hC 0))) with ⟨N,hN,hN'⟩,
    use N,split,{exact hN}, intros p hp,
    have h₁:f p - C < g p, linarith [(abs_lt.1 (hC p)).2],
    linarith [h₁,hN' p hp]
    },
{   intros hh D hD,
    rcases hh (D+C) (add_pos hD (lt_of_le_of_lt (abs_nonneg _) (hC 0))) with ⟨N,hN,hN'⟩,
    use N,split,{exact hN}, intros p hp,
    have h₁:g p - C < f p, linarith [(abs_lt.1 (hC p)).1],
    linarith [h₁,hN' p hp]}
end

@[simp]
def S.pos (T : S) : Prop := (T.func '' {n : ℤ | n > 0} ∩ {n : ℤ | n > 0}).infinite

lemma S.zero_nonpos : ¬S.pos 0 := 
begin 
    simp [set.infinite,not_not],
    rw [@set.nonempty.image_const _ _ ({n : ℤ | n > 0}) ⟨1,by norm_num⟩],
    apply @set.finite.subset _ ({0}:set ℤ) (set.finite_singleton 0) ({0} ∩ {n : ℤ | n > 0}),
    exact ({0}:set ℤ).inter_subset_left {n : ℤ | n > 0}
end


lemma S.add_pos {T₁ T₂ : S} : S.pos T₁ → S.pos T₂ → S.pos (T₁ + T₂) :=
λ hT₁ hT₂,
(lemma5_aux_iff _ (T₁ + T₂).AH).2
(λ C hC,let ⟨N,hN,hN'⟩:=lemma5_aux _ T₁.AH hT₁ C hC in 
let ⟨M,hM,hM'⟩:=lemma5_aux _ T₂.AH hT₂ C hC in
⟨max N M,lt_max_iff.2 (or.inl hN),λ p hp,calc
    (T₁ + T₂).func p 
            = T₁.func p + T₂.func p : rfl
        ... > C + C : add_lt_add (hN' _ (max_lt_iff.1 hp).1) (hM' _ (max_lt_iff.1 hp).2)
        ... > C : lt_add_of_pos_left C hC
    ⟩)

def E.pos (A : E) : Prop := quot.rec_on A (λ T,S.pos T) 
    (λ T₁ T₂ h,by simp at *;exact iff_infinite_pos_of_pos_of_bounded_difference _ _ T₁.AH T₂.AH h)


lemma pos_mk (T : S) : E.pos (mk T) ↔ S.pos T := iff.rfl

lemma pos_mk_setoid (T : S) : E.pos (quot.mk setoid.r T) ↔ S.pos T := iff.rfl

lemma neg_mk_setoid (T : S) : (-quot.mk setoid.r T:E) = quot.mk setoid.r (-T):= rfl


instance : pos_add_comm_group E := 
{ pos := λ A, E.pos A,
 zero_nonpos := by simp [pos_mk];exact S.zero_nonpos,
  add_pos := by repeat {refine λ a, quotient.induction_on a (λ _, _)};intros;exact S.add_pos a_1 a_2,
  pos_antisymm :=
  begin
    intro A,
    induction A with T,
    {   simp only [pos_mk_setoid,neg_mk_setoid,S.pos],
        rw [lemma5_aux_iff T.func T.AH,lemma5_aux_iff (-T).func (-T).AH],
        intro h,
        have h₁ : ∀ {p q r : Prop}, (p ∨ q ∨ r) ∧ (q ↔ r) ∧ (r → ¬q) ↔ (p ∧ ¬q ∧ ¬r), tauto,
        rw [neg_S_func_eq] at h,
        simp only [int_to_int_neg] at h,
        have h₂ : (∀ (C : ℤ), C > 0 → (∃ N>0, ∀ (p : ℤ), p > N → -T.func p > C)) ↔ 
            (∀ (C : ℤ), C > 0 → (∃ N>0, ∀ (p : ℤ), p > N → T.func p < -C)), simp [lt_neg],
        rw h₂ at h,
        have h₃ := h₁.1 ⟨lemma5 T.func T.AH, h,lemma5_not_ii_of_iii _⟩,
        apply quotient.eq.2,
        simp [(≈),setoid.r,bounded_difference],
        exact h₃.1},
    {   tauto}
  end,
  .. E.add_comm_group }

instance int_to_int.has_mul : has_mul (ℤ → ℤ) := ⟨λ f g, f ∘ g⟩

instance int_to_int.has_one : has_one (ℤ → ℤ) := ⟨id⟩

@[simp] 
lemma int_to_int.one_def : (1:ℤ → ℤ) = id := rfl

@[simp]
lemma int_to_int.mul_def (f g : ℤ → ℤ) : f * g = f ∘ g := rfl

lemma int_to_int.one_mul (f : ℤ → ℤ) : 1 * f = f := rfl

lemma int_to_int.mul_one (f : ℤ → ℤ) : f * 1 = f := rfl

lemma int_to_int.mul_assoc (f g h : ℤ → ℤ) : f * g * h = f * (g * h) := rfl

lemma int_to_int.right_distrib (f g h : ℤ → ℤ) : (f + g) * h = f * h + g * h := rfl

lemma almost_homomorphism_three (f : ℤ → ℤ) (hf : almost_homomorphism f) :
    ∃ C,∀ p q r, abs (f (p + q + r) - f p - f q - f r) < C :=
let ⟨C,hC⟩:=hf in ⟨C+C,λ p q r,calc
    abs (f (p + q + r) - f p - f q - f r) 
            = abs (f (p + q + r) - f (p + q) - f r + (f (p + q) - f p - f q)) : congr_arg abs (by ring)
        ... ≤ abs ( f (p + q + r) - f (p + q) - f r) + abs (f (p + q) - f p - f q) : abs_add _ _
        ... < C + C : add_lt_add (hC _ _) (hC _ _)  ⟩


lemma bounded_image (f : ℤ → ℤ) (g : ℤ → ℤ → ℤ) (hg : ∃ C,∀ p q,abs (g p q) < C) :
    ∃ C, ∀ p q, abs (f (g p q)) < C :=
let ⟨C,hC⟩:=hg in let ⟨E,hE⟩:=exists_max_of_ico f C (-C) 
(lt_trans (neg_lt_zero.2 (lt_of_le_of_lt (abs_nonneg _) (hC 0 0))) (lt_of_le_of_lt (abs_nonneg _) (hC 0 0))) in
⟨E,λ p q,hE _ (le_of_lt (abs_lt.1 (hC p q)).1) (abs_lt.1 (hC p q)).2⟩

lemma almost_homomorphism_mul (f g : ℤ → ℤ) 
    (hf : almost_homomorphism f) (hg : almost_homomorphism g) :
    almost_homomorphism (f * g) :=
let ⟨Cf,hCf⟩:=almost_homomorphism_three f hf in 
let ⟨E,hE⟩ := bounded_image f _ hg in
⟨Cf + E,λ p q, calc
    abs ((f * g) (p + q) - (f * g) p - (f * g) q) 
            = abs ( f (g (p + q)) - f (g p) - f (g q) ) : rfl
        ... = abs ( f (g p + g q + (g (p + q) - g p - g q)) - f (g p) - f (g q) - f (g (p + q) - g p - g q) + f (g (p + q) - g p - g q)) : congr_arg abs $ by simp;ring
        ... ≤ abs (f (g p + g q + (g (p + q) - g p - g q)) - f (g p) - f (g q) - f (g (p + q) - g p - g q)) + abs (f (g (p + q) - g p - g q)) : abs_add _ _
        ... < Cf + E : add_lt_add (hCf _ _ _) (hE _ _)⟩

instance : has_mul S := ⟨λ T₁ T₂, ⟨T₁.func*T₂.func,almost_homomorphism_mul _ _ T₁.AH T₂.AH⟩⟩

instance : has_one S := ⟨⟨1,⟨1,λ p q,by simp;exact int.one_pos⟩⟩⟩

@[simp]
lemma S.mul_func (T₁ T₂ : S) : (T₁ * T₂).func = T₁.func * T₂.func := rfl 
@[simp]
lemma S.one_mul (T :S) : 1 * T = T := func_eq rfl
@[simp]
lemma S.mul_one (T :S) : T * 1 = T := func_eq rfl
@[simp]
lemma S.mul_assoc (T₁ T₂ T₃ : S) : T₁ * T₂ * T₃ = T₁ * (T₂ * T₃) := rfl
@[simp]
lemma S.right_distrib (T₁ T₂ T₃ : S) : (T₁ + T₂) * T₃ = T₁ * T₃ + T₂ * T₃ := rfl


lemma aux_bounded_difference {f₁ f₂ : ℤ → ℤ} (h : bounded_difference f₁ f₂) :
∃ (g : ℤ → ℤ) (hg : ∃ C, ∀ p, abs (g p) < C), f₁ = f₂ + g :=
⟨f₁-f₂,h,eq_add_of_sub_eq' rfl⟩

lemma bounded_difference_mul {f₁ g₁ f₂ g₂ : ℤ → ℤ}
    (hf : bounded_difference f₁ f₂) (hg : bounded_difference g₁ g₂) (hf₂ : almost_homomorphism f₂) :
    bounded_difference (f₁ * g₁) (f₂ * g₂) :=
let ⟨Cf,hff⟩ := hf₂ in
let ⟨f,⟨Cf',hCf⟩,hhf⟩:=aux_bounded_difference hf in
let ⟨g,⟨Cg',hCg⟩,hhg⟩:=aux_bounded_difference hg in
let ⟨E,hE⟩:=exists_max_of_ico f₂ Cg' (-Cg')
(lt_trans (neg_lt_zero.2 (lt_of_le_of_lt (abs_nonneg (g 0)) (hCg 0))) (lt_of_le_of_lt (abs_nonneg (g 0)) (hCg 0))) in
⟨E + Cf + Cf' + 1,λ p,by rw [hhf,hhg];simp;
exact calc abs (f₂ (g₂ p + g p) + f (g₂ p + g p) - f₂ (g₂ p))
        = abs (f₂ (g₂ p + g p) - f₂ (g₂ p) + f (g₂ p + g p)) : congr_arg abs (by ring)
    ... ≤ abs (f₂ (g₂ p + g p) - f₂ (g₂ p)) + abs (f (g₂ p + g p)) : abs_add _ _
    ... ≤ abs (f₂ (g₂ p + g p) - f₂ (g₂ p)) + Cf' : add_le_add_left (le_of_lt (hCf _)) _
    ... = abs (f₂(g p) + (f₂ (g₂ p + g p) - f₂ (g₂ p) - f₂ (g p))) + Cf' : by simp;exact congr_arg abs (by ring)
    ... ≤ abs (f₂ (g p)) + abs (f₂ (g₂ p + g p) - f₂ (g₂ p) - f₂ (g p)) + Cf' : add_le_add_right (abs_add _ _) _
    ... ≤ abs (f₂ (g p)) + Cf + Cf' : add_le_add_right (add_le_add_left (le_of_lt (hff _ _)) _) _
    ... ≤ E + Cf + Cf' : add_le_add_right (add_le_add_right (le_of_lt (hE _ (le_of_lt (abs_lt.1 (hCg _)).1) ((abs_lt.1 (hCg _)).2))) _) _
    ... < E + Cf + Cf' + 1 : lt_add_one (E + Cf + Cf')⟩

instance : has_one E := ⟨mk 1⟩

instance : has_mul E := ⟨λ x y,quotient.lift_on₂ x y (λ F G, mk (F * G)) $
    λ F₁ G₁ F₂ G₂ hF hG, quotient.sound $
    (by dsimp [(≈),setoid.r] at *;exact bounded_difference_mul hF hG F₂.AH)⟩

@[simp] theorem mk_mul (F G : S) : mk F * mk G = mk (F * G) := rfl
@[simp] theorem mk_one : 1 = mk 1  := rfl


@[simp]
lemma E.mul_func (T₁ T₂ : E) : (T₁ * T₂) = T₁ * T₂ := rfl 
@[simp]
lemma E.one_mul: ∀ T:E, 1 * T = T := by repeat {refine λ a, quotient.induction_on a (λ _, _)};simp
@[simp]
lemma E.mul_one: ∀ T:E, T * 1 = T := by repeat {refine λ a, quotient.induction_on a (λ _, _)};simp
@[simp]
lemma E.mul_assoc : ∀ (T₁ T₂ T₃ : E), T₁ * T₂ * T₃ = T₁ * (T₂ * T₃) := by repeat {refine λ a, quotient.induction_on a (λ _, _)};simp
@[simp]
lemma E.right_distrib : ∀ (T₁ T₂ T₃ : E), (T₁ + T₂) * T₃ = T₁ * T₃ + T₂ * T₃ := by repeat {refine λ a, quotient.induction_on a (λ _, _)};simp

lemma lemma7_aux {f : ℤ → ℤ} {C : ℤ} (hC : ∀ (p q : ℤ), abs (f (p + q) - f p - f q) < C) : ∀ p q,abs (f (p*q) - p * f q) < ( abs p + 1) * C :=
λ p q,
have h₂:∀ p,abs (f ((p+1)*q) - f (p*q) - f q) < C,from λp, calc
    abs (f ((p+1)*q) - f (p*q) - f q) 
            = abs (f (p*q + q) - f (p*q) - f q) : by rw [right_distrib,one_mul]
        ... < C : hC _ _,
have h₂':∀ p:ℕ,abs (f ((-↑p - 1) * q) - f (-↑p * q) + f q) < C,from λp, calc
    abs (f ((-↑p - 1) * q) - f (-↑p * q) + f q)
            = abs (- (f ((-↑p-1)*q + q) - f ((-↑p-1)*q) - f q)) : have hh: (-↑p - 1) * q + q=-p*q,from by ring,congr_arg abs (by rw [hh];ring)
        ... = abs (f ((-↑p-1)*q + q) - f ((-↑p-1)*q) - f q) : abs_neg _
        ... < C : hC _ _,
int.induction_on p (by have h₁:=hC 0 0;simp at *;exact h₁) 
    (λ i hi,calc
    abs (f ((↑i + 1) * q) - (↑i + 1) * f q)
            = abs ((f ((↑i + 1) * q) - f (↑i * q) - f q) + (f (↑i * q) - ↑i * f q)) : congr_arg abs (by ring)
        ... ≤ abs (f ((↑i + 1) * q) - f (↑i * q) - f q) + abs (f (↑i * q) - ↑i * f q) : abs_add _ _
        ... < C + (abs ↑i + 1) * C : add_lt_add (h₂ _) hi
        ... = ( abs ↑i + 1 + 1) * C: by ring
        ... = ( abs ↑(i + 1) + 1) * C : have h₃:abs (↑i:ℤ) = ↑i,from abs_of_nonneg (int.coe_zero_le i),
                                        have h₃':abs (↑i+1:ℤ) = ↑i+1,from abs_of_nonneg (int.coe_zero_le _),
                                    by simp [h₃,h₃'])
    (λ i hi,by simp at *;exact calc
    abs (f ((-↑i - 1) * q) - (-↑i - 1) * f q) 
            = abs ((f ((-↑i - 1) * q) - f (-↑i * q) + f q) + (f (-↑i * q) - -↑i * f q)) : congr_arg abs (by ring)
        ... ≤ abs (f ((-↑i - 1) * q) - f (-↑i * q) + f q) + abs (f (-↑i * q) - -↑i * f q) : abs_add _ _
        ... < C + (↑i + 1) * C : have hh':∀ q:ℤ,-(↑i * q)=-↑i * q,from λq,neg_mul_eq_neg_mul ↑i q,add_lt_add (hh' q ▸ h₂' i) (by rw [←hh',←hh',sub_neg_eq_add];exact hi)
        ... = (↑(i + 1) + 1) * C : by ring
        ... = (abs (↑(i + 1)) + 1) * C : by rw [abs_of_nonneg (int.coe_zero_le (i+1))]
        ... = (abs (-(↑i + 1)) + 1)*C:by ring
        ... = (abs (-↑i - 1) + 1) * C : by rw [neg_add,←sub_eq_add_neg])


lemma lemma7 {f : ℤ → ℤ} (C : ℤ) (hC : ∀ (p q : ℤ), abs (f (p + q) - f p - f q) < C) : ∀ p q, abs (p * f q - q * f p) < (abs p + abs q + 2) * C :=
λ p q,
begin
have h₁ := lemma7_aux hC p q,
have h₂ := lemma7_aux hC q p,
rw [←abs_neg,neg_sub,mul_comm p q] at h₁,
exact calc abs (p * f q - q * f p) 
        ≤ abs (p * f q - f (q * p)) + abs (f (q * p) - q * f p) : abs_sub_le _ _ _
    ... < (abs p + 1) * C + (abs q + 1) * C : add_lt_add h₁ h₂ 
    ... = (abs p + abs q + 2) * C : by ring
end

lemma upper_bound {f : ℤ → ℤ} (hf : almost_homomorphism f) : ∃ A B,∀ p,abs (f p) < A * abs p + B :=
let ⟨C,hC⟩:=hf in ⟨C + abs (f 1),3*C,λ p,
begin
    have h₁:=lemma7 C hC p 1,
    simp [abs_sub] at h₁,ring at h₁,rw [mul_comm (f 1)] at h₁,
    exact calc 
        abs (f p) = abs (f p - p * f 1 + p * f 1) : by ring
            ... ≤ abs (f p - p * f 1) + abs (p * f 1) : abs_add _ _
            ... < C * abs p + 3 * C + abs (p * f 1) : add_lt_add_right h₁ _
            ... = (C + abs (f 1)) * abs p + 3 * C : by rw [abs_mul];ring
end⟩

--lemma mul_eq_mk (A B : S) : (quot.mk setoid.r A:E) * (quot.mk setoid.r B:E) = quot.mk setoid.r B * quot.mk setoid.r A
@[simp]
lemma E.mul_comm (F G : E) : F * G = G * F :=
begin
induction F with f,induction G with g,
{refine mk_eq.mpr _,
simp [(≈),setoid.r],
rcases upper_bound f.AH with ⟨A,B,hf⟩,
rcases upper_bound g.AH with ⟨C,D,hg⟩,
rcases f.AH with ⟨Cf,hCf⟩,
rcases g.AH with ⟨Cg,hCg⟩,
set C':=max Cf Cg,
use max ((B + D + 4) * C' + (2 + A + C) * C' + 1) (abs (f.func (g.func 0) - g.func (f.func 0))+1),
intro p,
by_cases hp:p=0,
{   simp [hp],
    exact or.inr int.one_pos},
{
have h₁:=lemma7 C' (λ p q,lt_of_lt_of_le (hCf p q) (le_max_left _ _)) p (g.func p),
have h₂:=lemma7 C' (λ p q,lt_of_lt_of_le (hCg p q) (le_max_right _ _)) p (f.func p),
rw [abs_sub,mul_comm (f.func p)] at h₂,
have h₃:abs (p)*abs(f.func (g.func p) - g.func (f.func p)) < ((2 + A + C)*C') * abs p + (B + D + 4)*C',
    from calc
        abs p * abs (f.func (g.func p) - g.func (f.func p))     
            = abs (p*f.func (g.func p) - p*g.func (f.func p)) : by rw [←abs_mul,mul_sub]
        ... ≤ abs (p * f.func (g.func p) - g.func p * f.func p) + abs (g.func p * f.func p - p * g.func (f.func p)) : abs_sub_le _ _ _
        ... < (abs p + abs (g.func p) + 2) * C' + (abs p + abs (f.func p) + 2) * C' : add_lt_add h₁ h₂
        ... = ( 2*abs p + abs (f.func p) + abs (g.func p) + 4)*C' : by ring
        ... < (2*abs p + (A * abs p + B) + (C * abs p + D) + 4) * C' : 
            mul_lt_mul_of_pos_right (add_lt_add_right (add_lt_add (add_lt_add_left (hf p) _) (hg p)) _)
            (lt_max_iff.2 (or.inl (lt_of_le_of_lt (abs_nonneg _) (hCf 1 1))))
        ... = ((2 + A + C)*C') * abs p + (B + D + 4)*C' : by ring,
rw [mul_comm (abs p)] at h₃,
have B_nonneg : B ≥ 0,{
have h':=hf 0, simp at h',
exact le_of_lt (lt_of_le_of_lt (abs_nonneg _) h')
},
have D_nonneg : D ≥ 0,{
have h':=hg 0, simp at h',
exact le_of_lt (lt_of_le_of_lt (abs_nonneg _) h')
},
have C'_nonneg : C'≥0,{
    exact le_max_left_of_le (le_of_lt (lt_of_le_of_lt (abs_nonneg _) (hCf 0 0)))
},
have h₄:=int.le_div_of_mul_le (abs_pos.mpr hp) (le_of_lt h₃),
rw [add_comm ((2 + A + C) * C' * abs p),int.add_mul_div_right _ _ (mt ((@abs_eq_zero _ _ p).1) hp)] at h₄,
exact calc
abs ((f.func ∘ g.func) p - (g.func ∘ f.func) p)
        ≤ (B + D + 4) * C' / abs p + (2 + A + C) * C' : h₄
    ... ≤ (B + D + 4) * C' + (2 + A + C) * C' : add_le_add_right (int.div_le_self _ 
    (mul_nonneg (add_nonneg (add_nonneg B_nonneg D_nonneg) (by norm_num)) C'_nonneg)) _
    ... < (B + D + 4) * C' + (2 + A + C) * C' + 1 : lt_add_one ((B + D + 4) * C' + (2 + A + C) * C')
    ... ≤ max ((B + D + 4) * C' + (2 + A + C) * C' + 1) (abs (f.func (g.func 0) - g.func (f.func 0))+1) : le_max_left _ _,
},
},
{refl},{refl}
end

@[simp]
lemma E.left_distrib : ∀ (T₃ T₁ T₂ : E), T₃ * (T₁ + T₂) = T₃ * T₁ + T₃ * T₂ :=
λ T₃ T₁ T₂,by rw [E.mul_comm,E.right_distrib,E.mul_comm,E.mul_comm T₂]

instance : comm_ring E := { add := _,
  mul := (*),
  mul_assoc := E.mul_assoc,
  one := 1,
  one_mul := E.one_mul,
  mul_one := E.mul_one,
  left_distrib := E.left_distrib,
  right_distrib := E.right_distrib,
  mul_comm := E.mul_comm,
  ..E.add_comm_group }

lemma almost_homomorphism_of_pos {f : ℤ → ℤ} 
    (h₁ : ∀ p<0, f p = - f (-p)) 
    (h₂:∃ C,∀ m n:ℕ, abs (f (m+n) - f m - f n) < C) :
    almost_homomorphism f := 
let ⟨C,hC⟩:=h₂ in ⟨C,λ p q,
begin
cases le_or_gt 0 p with hp hp;
cases le_or_gt 0 q with hq hq,
{   rcases int.eq_coe_of_zero_le hp with ⟨m,hm⟩,
    rcases int.eq_coe_of_zero_le hq with ⟨n,hn⟩,
    simp [hm,hn],
    exact hC _ _},
{   cases lt_or_ge (p+q) 0 with hpq hpq,
    {   have h₁:abs (f (p + q) - f p - f q) = abs (f (p + -(p+q)) - f p - f (-(p+q))),
        {rw [h₁ (p+q) hpq,h₁ q hq];simp;exact congr_arg abs (by ring)},
        rcases int.eq_coe_of_zero_le hp with ⟨m,hm⟩,
        rcases int.eq_coe_of_zero_le ((neg_nonneg.2 (le_of_lt hpq))) with ⟨n,hn⟩,
        rw [h₁,hn,hm],exact hC _ _},
    {   have h₁:abs (f (p + q) - f p - f q) = abs (f ((p+q) + -q) - f (p+q) - f (-q)),
        {rw [h₁ q hq];simp;rw [←abs_neg];exact congr_arg abs (by ring)},
        rcases int.eq_coe_of_zero_le hpq with ⟨m,hm⟩,
        rcases int.eq_coe_of_zero_le (neg_nonneg.2 (le_of_lt hq)) with ⟨n,hn⟩,
        rw [h₁,hm,hn],exact hC _ _}},
{   cases lt_or_ge (p+q) 0 with hpq hpq,
    {   have h₁:abs (f (p + q) - f p - f q) = abs (f (q + -(p+q)) - f q - f (-(p+q))),
        {rw [h₁ (p+q) hpq,h₁ p hp];simp;exact congr_arg abs (by ring)},
        rcases int.eq_coe_of_zero_le hq with ⟨m,hm⟩,
        rcases int.eq_coe_of_zero_le ((neg_nonneg.2 (le_of_lt hpq))) with ⟨n,hn⟩,
        rw [h₁,hn,hm],exact hC _ _},
    {   have h₁:abs (f (p + q) - f p - f q) = abs (f ((p+q) + -p) - f (p+q) - f (-p)),
        {rw [h₁ p hp];simp;rw [←abs_neg];exact congr_arg abs (by ring)},
        rcases int.eq_coe_of_zero_le hpq with ⟨m,hm⟩,
        rcases int.eq_coe_of_zero_le (neg_nonneg.2 (le_of_lt hp)) with ⟨n,hn⟩,
        rw [h₁,hm,hn],exact hC _ _}},
{   have hp':-p≥0,from (neg_nonneg.mpr (le_of_lt hp)),
    have hq':-q≥0,from (neg_nonneg.mpr (le_of_lt hq)),
    rcases int.eq_coe_of_zero_le hp' with ⟨m,hm⟩,
    rcases int.eq_coe_of_zero_le hq' with ⟨n,hn⟩,
    have h':abs (f (p + q) - f p - f q) = abs (f (-p + -q) - f (-p) - f (-q)),
    by rw [h₁ p hp,h₁ q hq,h₁ (p+q) (add_neg hp hq),neg_add,←abs_neg];exact congr_arg abs (by ring),
    rw [h',hm,hn], exact hC _ _}
end⟩

lemma quot_exists (F : E) : ∃ f:S, F = mk f := quot.induction_on F (λ f,⟨f,rfl⟩)

lemma exists_min_of_set_nat (s : set ℕ) (h : ∃ k,s k) : ∃ n:ℕ, n ∈ s ∧ ∀ m:ℕ, m ∈ s → n ≤ m :=
begin
use nat.find h,
split,
{   exact nat.find_spec h},
{   intro k,
    exact nat.find_min' h}
end

lemma exists_min (f : ℤ → ℤ) (hf:almost_homomorphism f) 
(h:(f '' {n : ℤ | n > 0} ∩ {n : ℤ | n > 0}).infinite) (p : ℤ) (hp : p ≥ 0): 
∃ n:ℤ, n>0 ∧ (f n ≥ p ∧ (∀ m>0,f m ≥ p → n ≤ m)) :=
begin
have hh := lemma5_aux' f hf h p hp,
simp at hh,
have hh_nat : ∃ (N : ℕ), 0 < N ∧ p ≤ f ↑N,
    from exists.elim hh (λ N hN,exists.elim (@int.eq_coe_of_zero_le N (le_of_lt hN.1)) 
    (λ M hM,exists.intro M (by rw [hM] at *;exact ⟨int.coe_nat_pos.mp hN.left,hN.2 _ (le_refl _)⟩))),
have hh':= exists_min_of_set_nat _ hh_nat,
rcases hh' with ⟨N,hN⟩, simp [(∈)] at hN, unfold set.mem at hN,
use N,split,
{   exact int.coe_nat_pos.mpr hN.1.1}, split,
{   exact hN.1.2},
intros m hm hm',
rcases @int.eq_coe_of_zero_le m (le_of_lt hm) with ⟨M,hM⟩,
rw [hM] at *,
apply int.coe_nat_le.2,
exact hN.2 _ ⟨int.coe_nat_pos.mp hm,hm'⟩
end


noncomputable def g (f : ℤ → ℤ) (hf:almost_homomorphism f) (h:(f '' {n : ℤ | n > 0} ∩ {n : ℤ | n > 0}).infinite): 
    ℤ → ℤ
| (int.of_nat n) := classical.some (exists_min f hf h ↑n (int.coe_zero_le n))
| (int.neg_succ_of_nat n) := - classical.some (exists_min f hf h (↑n+1) (int.coe_zero_le (n+1)))

lemma g_of_nat_def (f : ℤ → ℤ) (hf:almost_homomorphism f) (h:(f '' {n : ℤ | n > 0} ∩ {n : ℤ | n > 0}).infinite)
    (p : ℕ) : g f hf h ↑p = classical.some (exists_min f hf h ↑p (int.coe_zero_le p)) := rfl

lemma g_nonneg_def (f : ℤ → ℤ) (hf:almost_homomorphism f) (h:(f '' {n : ℤ | n > 0} ∩ {n : ℤ | n > 0}).infinite)
    (p : ℤ) (hp:p≥0) : g f hf h p = classical.some (exists_min f hf h p hp) := 
    exists.elim (int.eq_coe_of_zero_le hp) (λ p' hp',by simp [hp',g_of_nat_def])

lemma g_nonneg_def' (f : ℤ → ℤ) (hf:almost_homomorphism f) (h:(f '' {n : ℤ | n > 0} ∩ {n : ℤ | n > 0}).infinite)
    (p : ℤ) (hp:p≥0) : g f hf h p > 0 ∧ (f (g f hf h p) ≥ p ∧ (∀ m>0,f m ≥ p → (g f hf h p) ≤ m)) :=
    by simp [g_nonneg_def f hf h p hp];exact classical.some_spec (exists_min f hf h p hp)

lemma g_neg_def (f : ℤ → ℤ) (hf:almost_homomorphism f) (h:(f '' {n : ℤ | n > 0} ∩ {n : ℤ | n > 0}).infinite)
    (p : ℤ) (hp:p<0) : g f hf h p = - g f hf h (-p) := 
begin
    rcases int.eq_neg_succ_of_lt_zero hp with ⟨p',hp'⟩,
    rw [hp',int.neg_neg_of_nat_succ],
    refl
end

-- lemma g_almost_homomorphism (f : ℤ → ℤ) (hf:almost_homomorphism f) (h:(f '' {n : ℤ | n > 0} ∩ {n : ℤ | n > 0}).infinite) :
--     almost_homomorphism (g f hf h) :=
-- begin
-- apply almost_homomorphism_of_pos (g_neg_def f hf h),
-- simp,
-- end