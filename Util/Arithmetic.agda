module Util.Arithmetic where

open import Basic
open import Data.Nat.Base using (NonZero)
open import Data.Unit using (tt)
open import Relation.Nullary.Decidable.Core using (False)
open import Util.List



range : ℕ → List ℕ
range 0 = []
range (suc n) = n ∷ (range n)


{-
Alternative definitions of the standard ordering relations on ℕ
-}
_>'_ : ℕ → ℕ → Set
x >' y = Σ[ n ∈ ℕ ] (((1 + n) + y) ≡ x)

_≥'_ : ℕ → ℕ → Set
x ≥' y = (x ≡ y) ⊎ (x > y)

{-
More alternative definitions of the standard ordering on ℕ
-}
_≥''_ : ℕ → ℕ → Set
x ≥'' y = Σ[ n ∈ ℕ ] ((n + y) ≡ x)

_>''_ : ℕ → ℕ → Set
x >'' y = x ≥'' (1 + y)


_le_ : ℕ → ℕ → Bool
0 le y = true
(suc x) le 0 = false
(suc x) le (suc y) = x le y

_ge_ : ℕ → ℕ → Bool
x ge y = y le x

_gt_ : ℕ → ℕ → Bool
x gt y = y lt x



list-max : (l : List ℕ) → ℕ
list-max [] = 0
list-max (x ∷ xs) = max x (list-max xs)


min-Nat : (ℕ → Set) → ℕ → Set
min-Nat P n = (P n) × ((m : ℕ) → P m → n ≤ m)



Nat-Map : {A : Set} → (f : ℕ → A) → (n : ℕ) → Vec A n
Nat-Map {A} f 0 = []
Nat-Map {A} f (suc n) = (f n) ∷ (Nat-Map f n)

Nat-foldr : {A : Set} → (ℕ → A → A) → A → ℕ → A
Nat-foldr f z n = foldr f z (range n)


Nat-Map-list : {A : Set} → (ℕ → A) → ℕ → List A
Nat-Map-list f n = map f (range n)

{-
Nat-filter : {A : Set} → (ℕ → Maybe A) → ℕ → List A
Nat-filter f n = filter f (range n)
-}





-- solved with auto
x≮0 : {x : ℕ} → x ≮ 0
x≮0 = λ ()


-- not solved with auto
sx≠x : {x : ℕ} → (1 + x) ≢ x
sx≠x ()

{-
sx≠x₂ : {x : ℕ} → (1 + x) ≢ x
sx≠x₂ {0} = λ () -- solved with auto
sx≠x₂ {suc x} = {!!} -- not solved with auto
-}


ℕ-LEM : (n : ℕ) → (n ≡ 0) ⊎ (Σ[ m ∈ ℕ ] (n ≡ (suc m)))
ℕ-LEM 0 = inj₁ refl -- solved with auto
ℕ-LEM (suc n) = inj₂ (n , refl) -- solved with auto



x+1+y=1+x+y : (x y : ℕ) → x + (1 + y) ≡ 1 + (x + y)
x+1+y=1+x+y x y =
  x + (1 + y) ≡⟨ +-comm x (1 + y) ⟩
  (1 + y) + x ≡⟨ ≡-sym (+-assoc 1 y x) ⟩
  1 + (y + x) ≡⟨ cong suc (+-comm y x) ⟩
  1 + (x + y) ∎
  where open ≡-Reasoning



sx+y>y : (x y : ℕ) → ((1 + x) + y) > y
sx+y>y x 0 = s≤s z≤n
sx+y>y x (suc y) = begin-strict
  1 + y               <⟨ s≤s (sx+y>y x y) ⟩
  1 + ((1 + x) + y)   ≡⟨ ≡-sym (x+1+y=1+x+y (1 + x) y) ⟩
  (1 + x) + (1 + y)   ∎
  where
      open ≤-Reasoning

sx+y=sz→x+y=z : {x y z : ℕ} → ((1 + x) + y) ≡ (1 + z) → (x + y) ≡ z
sx+y=sz→x+y=z refl = refl



x>sy→x>y : {x y : ℕ} → x > suc y → x > y
x>sy→x>y {0} {y} ()
x>sy→x>y {(suc x)} {y} (s≤s hyp) = s≤s (≤-trans (n≤1+n y) hyp)


sx>sy→x>y : {x y : ℕ} → 1 + x > 1 + y → x > y
sx>sy→x>y {x} {y} (s≤s x>y) = x>y


min-Nat-unique : (P : ℕ → Set) → {x y : ℕ} → min-Nat P x → min-Nat P y → x ≡ y
min-Nat-unique P {x} {y} (Px , hyp-x) (Py , hyp-y) = ≤-antisym x≤y y≤x
  where
    x≤y = hyp-x y Py
    y≤x = hyp-y x Px

m<1+n+m : (m n : ℕ) → m < (1 + n) + m
m<1+n+m m n = m<n+m m (s≤s z≤n)

m<m+1+n : (m n : ℕ) → m < m + (1 + n)
m<m+1+n m n = m<m+n m (s≤s z≤n)

x+y-x=y : (x y : ℕ) → (x + y) - x ≡ y
x+y-x=y 0 y = refl
x+y-x=y (suc x) y = x+y-x=y x y

le→≤ : {m n : ℕ} → (m le n) ≡ true → m ≤ n
le→≤ {0} {n} hyp = z≤n
le→≤ {suc m} {0} ()
le→≤ {suc m} {suc n} hyp = s≤s (le→≤ hyp)

≤→le : {m n : ℕ} → m ≤ n → (m le n) ≡ true
≤→le {0} {n} z≤n = refl
≤→le {suc m} {0} ()
≤→le {suc m} {suc n} (s≤s m≤n) = ≤→le m≤n

lt→< : {m n : ℕ} → (m lt n) ≡ true → m < n
lt→< {m} {0} ()
lt→< {0} {suc n} hyp = s≤s (z≤n)
lt→< {suc m} {suc n} hyp = s≤s (lt→< hyp)

<→lt : {m n : ℕ} → m < n → (m lt n) ≡ true
<→lt {m} {0} ()
<→lt {0} {suc n} (s≤s z≤n) = refl
<→lt {suc m} {suc n} (s≤s m<n) = <→lt m<n

m⊔n≥n : (m n : ℕ) → (max m n) ≥ n
m⊔n≥n m 0 = z≤n
m⊔n≥n 0 (suc n) = ≤-refl
m⊔n≥n (suc m) (suc n) = s≤s (m⊔n≥n m n)

m⊔n≥m : (m n : ℕ) → (max m n) ≥ m
m⊔n≥m 0 n = z≤n
m⊔n≥m (suc m) (suc n) = s≤s (m⊔n≥m m n)
m⊔n≥m (suc m) 0 = ≤-refl


x+x≡2x : (x : ℕ) → x + x ≡ 2 * x
x+x≡2x x =
  x + x        ≡⟨ ≡-sym (+-identityʳ (x + x)) ⟩
  (x + x) + 0  ≡⟨ +-assoc x x 0 ⟩
  2 * x        ∎
    where open ≡-Reasoning


+ₗ-preserves-< : {m n : ℕ} → (x : ℕ) → m < n → (x + m) < (x + n)
+ₗ-preserves-< 0 m<n = m<n
+ₗ-preserves-< (suc x) m<n = s≤s (+ₗ-preserves-< x m<n)

+ᵣ-preserves-< : {m n : ℕ} → (x : ℕ) → m < n → (m + x) < (n + x)
+ᵣ-preserves-< {m} {n} x m<n = begin-strict
  m + x   ≡⟨ +-comm m x ⟩
  x + m   <⟨ +ₗ-preserves-< x m<n ⟩
  x + n   ≡⟨ +-comm x n ⟩
  n + x   ∎
  where
    open ≤-Reasoning

{-
ℕ-Poset : Poset lzero lzero lzero
ℕ-Poset = record{ Carrier = ℕ ; _≈_ = _≡_ ; _≤_ = _≤_ ; isPartialOrder = ≤-isPartialOrder }
-}

+ₗ-preserves-≤ : {x y : ℕ} → (m : ℕ) → x ≤ y → m + x ≤ m + y
+ₗ-preserves-≤ 0 x≤y = x≤y
+ₗ-preserves-≤ (suc m) x≤y = s≤s (+ₗ-preserves-≤ m x≤y)

+ᵣ-preserves-≤ : {x y : ℕ} → (m : ℕ) → x ≤ y → x + m ≤ y + m
+ᵣ-preserves-≤ {x} {y} m x≤y = begin
  x + m ≡⟨ +-comm x m ⟩
  m + x ≤⟨ +ₗ-preserves-≤ m x≤y ⟩
  m + y ≡⟨ +-comm m y ⟩
  y + m ∎
  where
    open ≤-Reasoning


*ₗ-preserves-≤ : {x y : ℕ} → (m : ℕ) → x ≤ y → m * x ≤ m * y
*ₗ-preserves-≤ 0 _ = z≤n
*ₗ-preserves-≤ {x} {y} (suc m) x≤y = begin
  (1 + m) * x   ≡⟨ refl ⟩
  x + (m * x)   ≤⟨ +ᵣ-preserves-≤ (m * x) x≤y ⟩
  y + (m * x)   ≤⟨ +ₗ-preserves-≤ y ind ⟩
  y + (m * y)   ≡⟨ refl ⟩
  (1 + m) * y   ∎ 
  where
    open ≤-Reasoning

    ind : (m * x) ≤ (m * y)
    ind = *ₗ-preserves-≤ m x≤y


*ᵣ-preserves-≤ : {x y : ℕ} → (m : ℕ) → x ≤ y → x * m ≤ y * m
*ᵣ-preserves-≤ {x} {y} m x≤y = begin
  x * m   ≡⟨ *-comm x m ⟩
  m * x   ≤⟨ *ₗ-preserves-≤ m x≤y ⟩
  m * y   ≡⟨ *-comm m y ⟩
  y * m   ∎
  where
    open ≤-Reasoning



offset-lemma : (n m x y : ℕ) → x < n → y < m → y + (x * m) < n * m
offset-lemma n m x y x<n y<m = begin-strict
  y + (x * m)   <⟨ +ᵣ-preserves-≤ (x * m) y<m ⟩
  m + (x * m)   ≡⟨ refl ⟩
  (1 + x) * m   ≤⟨ *ᵣ-preserves-≤ m x<n ⟩
  n * m         ∎ 
  where
    open ≤-Reasoning


n<1+n : (n : ℕ) → n < 1 + n
n<1+n 0 = (s≤s z≤n)
n<1+n (suc n) = s≤s (n<1+n n)

sub<-lemma : {n x : ℕ} → x < n → n - x > 0
sub<-lemma {0}     {_} ()
sub<-lemma {suc n} {0} 0<1+n = (s≤s z≤n)
sub<-lemma {suc n} {suc x} (s≤s x<n) = sub<-lemma x<n

sub≡-lemma : {n x : ℕ} → x ≤ n → n - x ≡ 0 → n ≡ x
sub≡-lemma {0} {0} 0≤0 0-0≡0 = refl
sub≡-lemma {0} {suc x} ()
sub≡-lemma {suc n} {0} 0≤1+n ()
sub≡-lemma {suc n} {suc x} (s≤s x≤n) n-x≡0 = cong suc (sub≡-lemma x≤n n-x≡0)

sub≡-lemma2 : {n x y : ℕ} → n - x ≡ (1 + y) → n - (1 + x) ≡ y
sub≡-lemma2 {n} {0} {y} n-0≡1+y = resp (λ a → a - 1 ≡ y) (≡-sym n-0≡1+y) refl
sub≡-lemma2 {0} {suc x} {y} () 
sub≡-lemma2 {suc n} {suc x} {y} 1+n-[1+x]≡1+y = sub≡-lemma2 {n} {x} {y} 1+n-[1+x]≡1+y


sub-suc-lemma : {n x : ℕ} → x < n → Σ[ y ∈ ℕ ] ((n - x) ≡ (1 + y))
sub-suc-lemma {0} {_} ()
sub-suc-lemma {suc n} {0} 0<1+n = n , refl
sub-suc-lemma {suc n} {suc x} (s≤s x<n) = sub-suc-lemma x<n

sub-suc-lemma2 : {n x y : ℕ} → (n - x) ≡ (1 + y) → x < n
sub-suc-lemma2 {0} {0} {_} ()
sub-suc-lemma2 {0} {suc x} {_} ()
sub-suc-lemma2 {suc n} {0} {_} _ = (s≤s z≤n)
sub-suc-lemma2 {suc n} {suc x} {y} 1+n-[1+x]≡1+y = (s≤s (sub-suc-lemma2 1+n-[1+x]≡1+y))


suc<-lemma : {m n : ℕ} → m < n → Σ[ k ∈ ℕ ] (n ≡ 1 + k)
suc<-lemma {_} {0} ()
suc<-lemma {_} {suc n} _ = n , refl



list-max-is-max : (l : List ℕ) → (i : Fin (length l)) → (list-max l) ≥ (lookup l i)
list-max-is-max [] ()
list-max-is-max (x ∷ xs) zero = resp (λ y → (list-max (x ∷ xs)) ≥ y) refl (m⊔n≥m x (list-max xs))
list-max-is-max l@(x ∷ xs) 1+i@(suc i) = begin
  lookup l 1+i   ≡⟨ refl ⟩
  lookup xs i    ≤⟨ list-max-is-max xs i ⟩
  list-max xs    ≤⟨ m⊔n≥n x (list-max xs) ⟩
  list-max l     ∎ 
  where
    open ≤-Reasoning


list-max-is-max2 : (l : List ℕ) → (i : ℕ) → (i<|l| : i < length l) → list-max l ≥ lookup< l i i<|l|
list-max-is-max2 [] _ ()
list-max-is-max2 l@(x ∷ xs) 0 0<|l| = m⊔n≥m x (list-max xs)
list-max-is-max2 l@(x ∷ xs) (suc n) 1+n<|l|@(s≤s n<|xs|) = begin
  lookup< l (1 + n) 1+n<|l|   ≡⟨ refl ⟩
  lookup< xs n n<|xs|         ≤⟨ list-max-is-max2 xs n n<|xs| ⟩
  list-max xs                 ≤⟨ m⊔n≥n x (list-max xs) ⟩
  list-max l                  ∎
  where
    open ≤-Reasoning


sub<-lemma2 : {n x : ℕ} → x < n → n - (1 + x) < n
sub<-lemma2 {0}     {_}    ()
sub<-lemma2 {suc n} {0}     _         = n<1+n n
sub<-lemma2 {suc n} {suc x} (s≤s x<n) = begin-strict
  (1 + n) - (2 + x)   ≡⟨ refl ⟩
  n - (1 + x)         <⟨ sub<-lemma2 x<n ⟩
  n                   <⟨ n<1+n n ⟩
  1 + n               ∎
  where
    open ≤-Reasoning

{-proof
  where
    x<n → n - (1 + x) < n 
    proof
  -}

0-x≡0 : (x : ℕ) → 0 - x ≡ 0
0-x≡0 0 = refl
0-x≡0 (suc x) = refl

sub-assoc : (x y z : ℕ) → x - (y + z) ≡ (x - y) - z
sub-assoc 0 y z =
  0 - (y + z)   ≡⟨ 0-x≡0 (y + z) ⟩
  0             ≡⟨ ≡-sym (0-x≡0 z) ⟩
  0 - z         ≡⟨ ≡-sym (cong (λ w → w - z) (0-x≡0 y)) ⟩
  (0 - y) - z   ∎
  where
    open ≡-Reasoning
sub-assoc (suc x) 0 z = cong (λ w → w - z) refl 
sub-assoc (suc x) (suc y) z = sub-assoc x y z

sub-suc-lemma3 : (x y : ℕ) → y ≤ x → (1 + x) - y ≡ 1 + (x - y)
sub-suc-lemma3 x       0       _                  = refl
sub-suc-lemma3 0       (suc y) ()
sub-suc-lemma3 (suc x) (suc y) 1+y≤1+x@(s≤s y≤x)  = sub-suc-lemma3 x y y≤x

x-y≤x : (x y : ℕ) → x - y ≤ x
x-y≤x x       0       = ≤-refl
x-y≤x 0       (suc y) = z≤n
x-y≤x (suc x) (suc y) = begin
  (1 + x) - (1 + y) ≡⟨ refl ⟩
  x - y             ≤⟨ x-y≤x x y ⟩
  x                 ≤⟨ n≤1+n x ⟩
  1 + x             ∎
  where
    open ≤-Reasoning


sub<-lemma3 : (x y z : ℕ) → y ≤ x → y - z ≤ x
sub<-lemma3 x y z y≤x = begin
  y - z   ≤⟨ x-y≤x y z ⟩
  y       ≤⟨ y≤x ⟩
  x       ∎
  where
    open ≤-Reasoning


sub-assoc2 : (x y z : ℕ) → z ≤ y → y ≤ x → x - (y - z) ≡ (x - y) + z
sub-assoc2 0       0      0       z≤n z≤n = refl
sub-assoc2 _       0      (suc z) ()
sub-assoc2 0       (suc y) _      _   ()
sub-assoc2 (suc x) y       0      0≤y y≤1+x =
  (1 + x) - (y - 0)   ≡⟨ refl ⟩
  (1 + x) - y         ≡⟨ ≡-sym (+-identityʳ ((1 + x) - y)) ⟩
  ((1 + x) - y) + 0   ∎
  where
    open ≡-Reasoning
sub-assoc2 (suc x) (suc y) (suc z) 1+z≤1+y@(s≤s z≤y) 1+y≤1+x@(s≤s y≤x) =
  (1 + x) - ((1 + y) - (1 + z))  ≡⟨ refl ⟩
  (1 + x) - (y - z)              ≡⟨ sub-suc-lemma3 x (y - z) y-z≤x ⟩ 
  1 + (x - (y - z))              ≡⟨ cong suc (sub-assoc2 x y z z≤y y≤x) ⟩
  1 + ((x - y) + z)              ≡⟨ +-comm 1 ((x - y) + z) ⟩
  ((x - y) + z) + 1              ≡⟨ +-assoc (x - y) z 1 ⟩
  (x - y) + (z + 1)              ≡⟨ cong (λ w → (x - y) + w) (+-comm z 1) ⟩
  (x - y) + (1 + z)              ≡⟨ refl ⟩
  ((1 + x) - (1 + y)) + (1 + z)   ∎
  where
    open ≡-Reasoning
    
    y-z≤x : (y - z) ≤ x
    y-z≤x = ≤-trans (x-y≤x y z) y≤x

pred≤-lemma : {x y : ℕ} → x < y → x ≤ (y - 1)
pred≤-lemma {_} {0} ()
pred≤-lemma {x} {suc y} x<1+y@(s≤s x≤y) = x≤y

x-x≡0 : (x : ℕ) → x - x ≡ 0
x-x≡0 0 = refl
x-x≡0 (suc x) = x-x≡0 x

diff : ℕ → ℕ → ℕ
diff 0       0       = 0
diff (suc x) 0       = suc x
diff 0       (suc y) = suc y
diff (suc x) (suc y) = diff x y

diff[0,x]≡x : (x : ℕ) → diff 0 x ≡ x
diff[0,x]≡x 0 = refl
diff[0,x]≡x (suc x) = refl

diff[x,0]≡x : (x : ℕ) → diff x 0 ≡ x
diff[x,0]≡x 0 = refl
diff[x,0]≡x (suc x) = refl

diff[x,x]≡0 : (x : ℕ) → diff x x ≡ 0
diff[x,x]≡0 0 = refl
diff[x,x]≡0 (suc x) = diff[x,x]≡0 x

x≢y→diff[x,y]>0 : {x y : ℕ} → x ≢ y → diff x y > 0
x≢y→diff[x,y]>0 {0} {0} 0≢0 = ⊥-elim (0≢0 refl)
x≢y→diff[x,y]>0 {suc x} {0} _ = s≤s z≤n
x≢y→diff[x,y]>0 {0} {suc y} _ = s≤s z≤n
x≢y→diff[x,y]>0 {suc x} {suc y} 1+x≢1+y = x≢y→diff[x,y]>0 x≢y
  where
    x≢y : x ≢ y
    x≢y x≡y = 1+x≢1+y (cong suc x≡y)

diff[x,y]>0→x≢y : {x y : ℕ} → diff x y > 0 → x ≢ y
diff[x,y]>0→x≢y {0} {0} ()
diff[x,y]>0→x≢y {suc x} {0} _ ()
diff[x,y]>0→x≢y {0} {suc y} _ ()
diff[x,y]>0→x≢y {suc x} {suc y} diff[1+x,1+y]>0 1+x≡1+y = diff[x,y]>0→x≢y diff[1+x,1+y]>0 (suc-injective 1+x≡1+y)

diff+-lemma : (x y z : ℕ) → diff (x + y) (x + z) ≡ diff y z
diff+-lemma 0       _ _ = refl
diff+-lemma (suc x) y z = diff+-lemma x y z



*-distributes-diffₗ : (x₁ x₂ y : ℕ) → diff (y * x₁) (y * x₂) ≡ y * (diff x₁ x₂)
*-distributes-diffₗ _ _ 0 = refl
*-distributes-diffₗ 0 x₂ (suc y) =
  diff ((1 + y) * 0) ((1 + y) * x₂) ≡⟨ cong (λ w → diff w ((1 + y) * x₂)) (*-zeroʳ (1 + y)) ⟩
  diff 0 ((1 + y) * x₂)             ≡⟨ diff[0,x]≡x ((1 + y) * x₂) ⟩
  (1 + y) * x₂                      ≡⟨ cong (λ w → (1 + y) * w) (≡-sym (diff[0,x]≡x x₂)) ⟩
  (1 + y) * (diff 0 x₂)             ∎
  where
    open ≡-Reasoning
*-distributes-diffₗ (suc x₁) 0 (suc y) =
  diff ((1 + y) * (1 + x₁)) ((1 + y) * 0) ≡⟨ cong (λ w → diff ((1 + y) * (1 + x₁)) w) (*-zeroʳ (1 + y)) ⟩
  diff ((1 + y) * (1 + x₁)) 0             ≡⟨ diff[x,0]≡x ((1 + y) * (1 + x₁)) ⟩
  (1 + y) * (1 + x₁)                      ≡⟨ cong (λ w → (1 + y) * w) (≡-sym (diff[x,0]≡x (1 + x₁))) ⟩
  (1 + y) * (diff (1 + x₁) 0)             ∎
  where
    open ≡-Reasoning
*-distributes-diffₗ (suc x₁) (suc x₂) (suc y) =
  diff ((1 + y) * (1 + x₁)) ((1 + y) * (1 + x₂)) ≡⟨ cong (λ w → diff w ((1 + y) * (1 + x₂))) (*-comm (1 + y) (1 + x₁)) ⟩
  diff ((1 + x₁) * (1 + y)) ((1 + y) * (1 + x₂)) ≡⟨ cong (λ w → diff ((1 + x₁) * (1 + y)) w) (*-comm (1 + y) (1 + x₂)) ⟩
  diff ((1 + x₁) * (1 + y)) ((1 + x₂) * (1 + y)) ≡⟨ refl ⟩
  diff ((1 + y) + (x₁ * (1 + y))) ((1 + y) + (x₂ * (1 + y))) ≡⟨ diff+-lemma (1 + y) (x₁ * (1 + y)) (x₂ * (1 + y)) ⟩
  diff (x₁ * (1 + y)) (x₂ * (1 + y))             ≡⟨ cong (λ w → diff w (x₂ * (1 + y))) (*-comm x₁ (1 + y)) ⟩
  diff ((1 + y) * x₁) (x₂ * (1 + y))             ≡⟨ cong (λ w → diff ((1 + y) * x₁) w) (*-comm x₂ (1 + y)) ⟩
  diff ((1 + y) * x₁) ((1 + y) * x₂)             ≡⟨ *-distributes-diffₗ x₁ x₂ (1 + y) ⟩
  (1 + y) * (diff x₁ x₂)                         ≡⟨ refl ⟩
  (1 + y) * (diff (1 + x₁) (1 + x₂))             ∎
  where
    open ≡-Reasoning




divmod-uniqueness-lemma : (x y n : ℕ) →  x % (1 + n) ≡ y % (1 + n) → x / (1 + n) ≡ y / (1 + n) → x ≡ y
divmod-uniqueness-lemma x y n x%[1+n]≡y%[1+n] x/[1+n]≡y/[1+n] =
  x                                              ≡⟨ m≡m%n+[m/n]*n x n ⟩
  (x % (1 + n)) + ((x / (1 + n)) * (1 + n))      ≡⟨ cong (λ w → w + ((x / (1 + n)) * (1 + n))) x%[1+n]≡y%[1+n] ⟩
  (y % (1 + n)) + ((x / (1 + n)) * (1 + n))      ≡⟨ cong (λ w → (y % (1 + n)) + w) (cong (λ w → w * (1 + n)) x/[1+n]≡y/[1+n]) ⟩
  (y % (1 + n)) + ((y / (1 + n)) * (1 + n))      ≡⟨ ≡-sym (m≡m%n+[m/n]*n y n) ⟩
  y                                              ∎
  where
    open ≡-Reasoning

m<1+n→m%[1+n]≡m : {m n : ℕ} → m < (1 + n) → m % (1 + n) ≡ m
m<1+n→m%[1+n]≡m m<1+n@(s≤s m≤n) = m≤n⇒m%n≡m m≤n


divmod-lemma : (w x y n : ℕ) → y < (1 + n) → w ≡ y + x * (1 + n) → y ≡ w % (1 + n) × x ≡ w / (1 + n)
divmod-lemma w x y n y<1+n w≡y+x*[1+n] = y≡w%[1+n] , x≡w/[1+n]
  where
    y%[1+n]≡y : y % (1 + n) ≡ y
    y%[1+n]≡y = m<1+n→m%[1+n]≡m y<1+n

    w%[1+n]≡y : w % (1 + n) ≡ y
    w%[1+n]≡y =
      w % (1 + n)                  ≡⟨ cong (λ h → h % (1 + n)) w≡y+x*[1+n] ⟩
      (y + x * (1 + n)) % (1 + n)  ≡⟨ [m+kn]%n≡m%n y x n ⟩
      y % (1 + n)                  ≡⟨ y%[1+n]≡y ⟩
      y                            ∎
      where
        open ≡-Reasoning

    sublemma1 : y % (1 + n) + (x * (1 + n)) % (1 + n) < 1 + n
    sublemma1 = begin-strict
      y % (1 + n) + (x * (1 + n)) % (1 + n) ≡⟨ cong (λ h → y % (1 + n) + h) (m*n%n≡0 x n) ⟩
      y % (1 + n) + 0                       ≡⟨ +-identityʳ (y % (1 + n)) ⟩
      y % (1 + n)                           ≡⟨ y%[1+n]≡y ⟩
      y                                     <⟨ y<1+n ⟩
      1 + n                                 ∎
      where
        open ≤-Reasoning

    w/[1+n]≡x : w / (1 + n) ≡ x
    w/[1+n]≡x =
      w / (1 + n)                                ≡⟨ cong (λ h → h / (1 + n))  w≡y+x*[1+n] ⟩
      (y + x * (1 + n)) / (1 + n)                ≡⟨ +-distrib-/ y (x * (1 + n)) sublemma1 ⟩
      (y / (1 + n)) + (( x * (1 + n)) / (1 + n)) ≡⟨ cong (λ h → h + (( x * (1 + n)) / (1 + n))) ( m<n⇒m/n≡0 y<1+n ) ⟩ 
      (( x * (1 + n)) / (1 + n))                 ≡⟨  m*n/n≡m x (1 + n) ⟩
      x                                          ∎
      where
        open ≡-Reasoning
        
    y≡w%[1+n] = ≡-sym w%[1+n]≡y
    x≡w/[1+n] = ≡-sym w/[1+n]≡x


{-
 TODO : simplify this to one case by using ¬ (x₁ ≡ x₂ × y₁ ≡ y₂)
-}
offset-uniqueness-lemma : {n m x₁ y₁ x₂ y₂ : ℕ} →  (y₁ < m) → (y₂ < m) → y₁ + (x₁ * m) ≡ y₂ + (x₂ * m) → (x₁ ≡ x₂ × y₁ ≡ y₂)
offset-uniqueness-lemma {n} {m} {x₁} {y₁} {x₂} {y₂} y₁<m y₂<m w₁≡w₂ = x₁≡x₂ , y₁≡y₂
  where
    w₁ = y₁ + (x₁ * m)
    w₂ = y₂ + (x₂ * m)

    sublemma1 : Σ[ m' ∈ ℕ ] (m ≡ 1 + m')
    sublemma1 = suc<-lemma y₁<m

    m' = proj₁ sublemma1
    m≡1+m' = proj₂ sublemma1

    y₁<1+m' : y₁ < 1 + m'
    y₁<1+m' = begin-strict
      y₁       <⟨ y₁<m ⟩
      m        ≡⟨ m≡1+m' ⟩
      1 + m'   ∎
      where
        open ≤-Reasoning

    y₂<1+m' : y₂ < 1 + m'
    y₂<1+m' = begin-strict
      y₂       <⟨ y₂<m ⟩
      m        ≡⟨ m≡1+m' ⟩
      1 + m'   ∎
      where
        open ≤-Reasoning
    

    w₁' = y₁ + (x₁ * (1 + m'))
    w₂' = y₂ + (x₂ * (1 + m'))

    w₁≡w₁' : w₁ ≡ w₁'
    w₁≡w₁' = cong (λ h → y₁ + (x₁ * h)) m≡1+m'

    w₂≡w₂' : w₂ ≡ w₂'
    w₂≡w₂' = cong (λ h → y₂ + (x₂ * h)) m≡1+m'

    w₁'≡w₂' : w₁' ≡ w₂'
    w₁'≡w₂' = ≡-trans (≡-sym w₁≡w₁') (≡-trans w₁≡w₂ w₂≡w₂')
    
    sublemma2 : y₁ ≡ w₁' % (1 + m') × x₁ ≡ w₁' / (1 + m')
    sublemma2 = divmod-lemma w₁' x₁ y₁ m' y₁<1+m' refl

    sublemma3 : y₂ ≡ w₂' % (1 + m') × x₂ ≡ w₂' / (1 + m')
    sublemma3 = divmod-lemma w₂' x₂ y₂ m' y₂<1+m' refl

    x₁≡x₂ = ≡-trans (proj₂ sublemma2) (≡-trans (cong (λ h → h / (1 + m')) w₁'≡w₂') (≡-sym (proj₂ sublemma3)))
    y₁≡y₂ = ≡-trans (proj₁ sublemma2) (≡-trans (cong (λ h → h % (1 + m')) w₁'≡w₂') (≡-sym (proj₁ sublemma3)))


offset-uniqueness-lemma2 : {n m x₁ y₁ x₂ y₂ : ℕ} →  (y₁ < m) → (y₂ < m) → ¬ (x₁ ≡ x₂ × y₁ ≡ y₂) → y₁ + (x₁ * m) ≢ y₂ + (x₂ * m)
offset-uniqueness-lemma2 {n} {m} {x₁} {y₁} {x₂} {y₂} y₁<m  y₂<m = contrapositive (offset-uniqueness-lemma {n} {m} {x₁} {y₁} {x₂} {y₂} y₁<m y₂<m)

ℕ-¬¬ : (x y : ℕ) → ¬ (¬ (x ≡ y)) → x ≡ y
ℕ-¬¬ 0       0 ¬¬0≡0 = refl
ℕ-¬¬ (suc x) 0 ¬¬1+x≡0 = ⊥-elim (¬¬1+x≡0 ¬1+x≡0)
  where
    ¬1+x≡0 : (1 + x) ≢ 0
    ¬1+x≡0 ()
ℕ-¬¬ 0 (suc y) ¬¬0≡1+y = ⊥-elim (¬¬0≡1+y ¬0≡1+y)
  where
    ¬0≡1+y : 0 ≢ (1 + y)
    ¬0≡1+y ()
ℕ-¬¬ (suc x) (suc y) ¬¬1+x≡1+y = 1+x≡1+y
  where
    ¬¬x≡y : ¬ (¬ (x ≡ y))
    ¬¬x≡y ¬x≡y = contradiction
      where
        ¬1+x≡1+y : ¬ (1 + x ≡ 1 + y)
        ¬1+x≡1+y 1+x≡1+y = ¬x≡y (suc-injective 1+x≡1+y)
        
        contradiction = ¬¬1+x≡1+y ¬1+x≡1+y
    
    x≡y : x ≡ y
    x≡y = ℕ-¬¬ x y ¬¬x≡y

    1+x≡1+y = cong suc x≡y

sub-suc-lemma5 : (x y : ℕ) → x < 1 + y → x ≤ y
sub-suc-lemma5 x y (s≤s x≤y) = x≤y

+-injective : (m : ℕ) → {x y : ℕ} → m + x ≡ m + y → x ≡ y
+-injective 0       x≡y     = x≡y
+-injective (suc m) 1+x≡1+y = +-injective m (suc-injective 1+x≡1+y)





*-injectiveₗ : (m : ℕ) → {x y : ℕ} → (1 + m) * x ≡ (1 + m) * y → x ≡ y
*-injectiveₗ m {0}     {0} _   = refl
*-injectiveₗ m {suc x} {0} hyp = ⊥-elim contradiction
  where
    sublemma1 : (1 + m) * (1 + x) ≡ 1 + (x + m * (1 + x))
    sublemma1 = refl

    sublemma2 : (1 + m) * (1 + x) ≢ 0
    sublemma2 ()

    sublemma3 : (1 + m) * 0 ≡ 0
    sublemma3 = *-zeroʳ (1 + m)

    sublemma4 : (1 + m) * (1 + x) ≡ 0
    sublemma4 = ≡-trans hyp sublemma3

    contradiction = sublemma2 sublemma4
*-injectiveₗ m {0} {suc y} hyp = ⊥-elim contradiction
  where
    sublemma1 : 0 ≡ (1 + m) * 0
    sublemma1 = ≡-sym (*-zeroʳ (1 + m))

    sublemma2 : 0 ≢ (1 + m) * (1 + y)
    sublemma2 ()

    sublemma3 : 0 ≡ (1 + m) * (1 + y)
    sublemma3 = ≡-trans sublemma1 hyp

    contradiction = sublemma2 sublemma3
*-injectiveₗ m {suc x} {suc y} hyp = proof
  where
    sublemma1 : (1 + m) + x * (1 + m) ≡ (1 + m) + y * (1 + m)
    sublemma1 =
      (1 + m) + x * (1 + m) ≡⟨ refl ⟩
      (1 + x) * (1 + m)     ≡⟨ *-comm (1 + x) (1 + m) ⟩
      (1 + m) * (1 + x)     ≡⟨ hyp ⟩
      (1 + m) * (1 + y)     ≡⟨ *-comm (1 + m) (1 + y) ⟩
      (1 + y) * (1 + m)     ≡⟨ refl ⟩
      (1 + m) + y * (1 + m) ∎
      where
        open ≡-Reasoning

    sublemma2 : (1 + m) * x ≡ (1 + m) * y
    sublemma2 =
      (1 + m) * x  ≡⟨ *-comm (1 + m) x ⟩
      x * (1 + m)  ≡⟨ +-injective (1 + m) sublemma1 ⟩
      y * (1 + m)  ≡⟨ *-comm y (1 + m) ⟩
      (1 + m) * y  ∎
      where
        open ≡-Reasoning

    proof = cong suc (*-injectiveₗ m {x} {y} sublemma2)



*-injectiveᵣ : (m : ℕ) → {x y : ℕ} → x * (1 + m) ≡ y * (1 + m) → x ≡ y
*-injectiveᵣ m {x} {y} hyp = *-injectiveₗ m [1+m]*x≡[1+m]*y 
  where
    [1+m]*x≡[1+m]*y : (1 + m) * x ≡ (1 + m) * y
    [1+m]*x≡[1+m]*y =
      (1 + m) * x   ≡⟨ *-comm (1 + m) x ⟩
      x * (1 + m)   ≡⟨ hyp ⟩
      y * (1 + m)   ≡⟨ *-comm y (1 + m) ⟩
      (1 + m) * y   ∎
      where
        open ≡-Reasoning


div<-lemma : (x y m : ℕ) → y < (1 + m) → (y + x * (1 + m)) / (1 + m) ≡ x
div<-lemma x y m y<1+m = ≡-sym (proj₂ (divmod-lemma  (y + x * (1 + m)) x y m y<1+m refl))
  
mod<-lemma : (x y m : ℕ) → y < (1 + m) → (y + x * (1 + m)) % (1 + m) ≡ y
mod<-lemma x y m y<1+m = ≡-sym (proj₁ (divmod-lemma  (y + x * (1 + m)) x y m y<1+m refl))

{-
-- Contrapositive of injectivity
divmod-uniqueness3 : (x y m : ℕ) → x ≢ y → x * (1 + m) ≢ y * (1 + m)
divmod-uniqueness3 x y m x≢y x*[1+m]≡y*[1+m] = x≢y (*-injectiveᵣ m x*[1+m]≡y*[1+m])
-}
{-
  
-}

divmod-uniqueness4 : (x₁ x₂ y m : ℕ) → y + x₁ * m ≢ y + x₂ * m → x₁ ≢ x₂
divmod-uniqueness4 x₁ x₂ y m hyp x₁≡x₂ = hyp (cong (λ x → y + x * m) x₁≡x₂)

divmod-uniqueness5 : (x y₁ y₂ m : ℕ) → y₁ + x * m ≢ y₂ + x * m → y₁ ≢ y₂
divmod-uniqueness5 x y₁ y₂ m hyp y₁≡y₂ = hyp (cong (λ y → y + x * m) y₁≡y₂)

divmod-uniqueness6 : (x₁ x₂ y₁ y₂ m : ℕ) → y₁ < (1 + m) → y₂ < (1 + m) → (y₁ + x₁ * (1 + m)) / (1 + m) ≢ (y₂ + x₂ * (1 + m)) / (1 + m) → x₁ ≢ x₂
divmod-uniqueness6 x₁ x₂ y₁ y₂ m y₁<1+m y₂<1+m hyp x₁≡x₂ = contradiction
  where
    sublemma1 : (y₁ + x₁ * (1 + m)) / (1 + m) ≡ x₁
    sublemma1 = div<-lemma x₁ y₁ m y₁<1+m

    sublemma2 : (y₂ + x₂ * (1 + m)) / (1 + m) ≡ x₂
    sublemma2 = div<-lemma x₂ y₂ m y₂<1+m

    sublemma3 : (y₁ + x₁ * (1 + m)) / (1 + m) ≡ (y₂ + x₂ * (1 + m)) / (1 + m)
    sublemma3 =
      (y₁ + x₁ * (1 + m)) / (1 + m)   ≡⟨ div<-lemma x₁ y₁ m y₁<1+m ⟩
      x₁                              ≡⟨ x₁≡x₂ ⟩
      x₂                              ≡⟨ ≡-sym (div<-lemma x₂ y₂ m y₂<1+m) ⟩
      (y₂ + x₂ * (1 + m)) / (1 + m)   ∎
      where
        open ≡-Reasoning
    
    contradiction = hyp sublemma3

ℕ≡-LEM : (x y : ℕ) → (x ≡ y) ⊎ (x ≢ y)
ℕ≡-LEM 0 0 = inj₁ refl
ℕ≡-LEM (suc x) 0 = inj₂ (λ ())
ℕ≡-LEM 0 (suc y) = inj₂ (λ ())
ℕ≡-LEM (suc x) (suc y) = sublemma (ℕ≡-LEM x y)
  where
    sublemma : (x ≡ y) ⊎ (x ≢ y) → (1 + x ≡ 1 + y) ⊎ (1 + x ≢ 1 + y)
    sublemma (inj₁ x≡y) = inj₁ (cong suc x≡y)
    sublemma (inj₂ x≢y) = inj₂ (λ 1+x≡1+y → x≢y (suc-injective 1+x≡1+y))



divmod-uniqueness7 : (x₁ x₂ y₁ y₂ m : ℕ) → y₁ + x₁ * m ≢ y₂ + x₂ * m → y₁ ≢ y₂ ⊎ x₁ ≢ x₂
divmod-uniqueness7 x₁ x₂ y₁ y₂ m hyp = sublemma (ℕ≡-LEM x₁ x₂)
  where
    sublemma : (x₁ ≡ x₂) ⊎ (x₁ ≢ x₂) → y₁ ≢ y₂ ⊎ x₁ ≢ x₂
    sublemma (inj₁ x₁≡x₂) = subsublemma (ℕ≡-LEM y₁ y₂)
      where
        subsublemma : (y₁ ≡ y₂) ⊎ (y₁ ≢ y₂) → y₁ ≢ y₂ ⊎ x₁ ≢ x₂
        subsublemma (inj₁ y₁≡y₂) = ⊥-elim (hyp subsubsublemma)
          where
            subsubsublemma : y₁ + x₁ * m ≡ y₂ + x₂ * m
            subsubsublemma =
              y₁ + x₁ * m   ≡⟨ cong (λ y → y + x₁ * m) y₁≡y₂ ⟩
              y₂ + x₁ * m   ≡⟨ cong (λ x → y₂ + x * m) x₁≡x₂ ⟩
              y₂ + x₂ * m   ∎
              where
                open ≡-Reasoning
        subsublemma (inj₂ y₁≢y₂) = inj₁ y₁≢y₂
        subproof = subsublemma (ℕ≡-LEM y₁ y₂)
    sublemma (inj₂ x₁≢x₂) = inj₂ x₁≢x₂


divmod-uniqueness2 : (x y m : ℕ) → x ≢ y → (x % (1 + m) ≢ y % (1 + m)) ⊎ ((x / (1 + m)) ≢ (y / (1 + m)))
divmod-uniqueness2 x y m x≢y = proof
  where
    x-def : x ≡ (x % (1 + m)) + ((x / (1 + m)) * (1 + m))
    x-def = m≡m%n+[m/n]*n x m

    y-def : y ≡ (y % (1 + m)) + ((y / (1 + m)) * (1 + m))
    y-def = m≡m%n+[m/n]*n y m

    sublemma : ((x % (1 + m)) + ((x / (1 + m)) * (1 + m))) ≢ ((y % (1 + m)) + ((y / (1 + m)) * (1 + m)))
    sublemma hyp = x≢y (≡-trans x-def (≡-trans hyp (≡-sym y-def)))
    
    proof = divmod-uniqueness7 (x / (1 + m)) (y / (1 + m)) (x % (1 + m)) (y % (1 + m)) (1 + m) sublemma

x≢0→NonZero-x : (x : ℕ) → x ≢ 0 → NonZero x
x≢0→NonZero-x 0         0≢0 = ⊥-elim (0≢0 refl)
x≢0→NonZero-x (suc x) 1+x≢0 = tt

x≢0→x≠0 : (x : ℕ) → x ≢ 0 → False (x ≟ 0)
x≢0→x≠0  0       0≢0 = ⊥-elim (0≢0 refl)
x≢0→x≠0 (suc x) 1+x≢0 = tt

divmod-uniqueness2< : (x y m : ℕ) → (m≠0 : False (m ≟ 0)) → x ≢ y → (_%_ x m { m≠0 } ≢ _%_ y m { m≠0 }) ⊎ ((_/_ x m {m≠0}) ≢ (_/_ y m {m≠0}))
divmod-uniqueness2< x y 0 ()
divmod-uniqueness2< x y (suc m) 1+m≢0 x≢y = divmod-uniqueness2 x y m x≢y



i<n*m→n≢0 : (i n m : ℕ) → i < n * m → n ≢ 0
i<n*m→n≢0 _ 0 _ ()
i<n*m→n≢0 _ (suc n) _ _ ()

i<n*m→m≢0 : (i n m : ℕ) → i < n * m → m ≢ 0
i<n*m→m≢0 i n m i<n*m = i<n*m→n≢0 i m n (resp (λ w → i < w) (*-comm n m) i<n*m)

/-<-≤-lemma : (x y m : ℕ) → (m≠0 : False (m ≟ 0)) → x ≤ y → _/_ x m {m≠0} ≤ _/_ y m {m≠0}
/-<-≤-lemma x y m m≠0 x≤y = /-mono-≤ {x} {y} {m} {m} {m≠0} {m≠0} x≤y ≤-refl

*<-lemma :
  (i n m : ℕ) →
  (i<n*m : i < n * m) →
  let m≠0 = (x≢0→x≠0 m (i<n*m→m≢0 i n m i<n*m))
  in
  (_/_ i m {m≠0}) < n
*<-lemma  i n 0 i<n*0 = ⊥-elim (x≮0 (resp (λ w → i < w) (*-zeroʳ n) i<n*0))
*<-lemma i 0 (suc m) i<0*[1+m] = ⊥-elim (x≮0 i<0*[1+m])
*<-lemma 0 (suc n) (suc m) hyp = s≤s z≤n
*<-lemma (suc i) (suc n) (suc m) hyp = proof
  where
    1+m≢0 : 1 + m ≢ 0
    1+m≢0 ()

    1+m≠0 : False (1 + m ≟ 0)
    1+m≠0 = x≢0→x≠0 (1 + m) 1+m≢0

    sublemma≤ : (1 + i) / (1 + m) ≤ (1 + n)
    sublemma≤ = begin
      (1 + i) / (1 + m)               ≤⟨ /-<-≤-lemma (1 + i) ((1 + n) * (1 + m)) (1 + m) 1+m≠0 (<⇒≤ hyp) ⟩
      ((1 + n) * (1 + m)) / (1 + m)   ≡⟨ m*n/n≡m (1 + n) (1 + m) ⟩
      (1 + n)                         ∎
      where
        open ≤-Reasoning

    sublemma≢ : (1 + i) / (1 + m) ≢ (1 + n)
    sublemma≢ hyp2 = contradiction
      where
        subsublemma : (1 + n) * (1 + m) < (1 + n) * (1 + m)
        subsublemma = begin-strict
          (1 + n) * (1 + m)                ≡⟨ ≡-sym (cong (λ w → w * (1 + m)) hyp2) ⟩
          ((1 + i) / (1 + m)) * (1 + m)    ≤⟨ m/n*n≤m (1 + i) (1 + m) ⟩
          1 + i                            <⟨ hyp ⟩
          (1 + n) * (1 + m)                ∎
          where
            open ≤-Reasoning
            
        contradiction = <-irrefl refl subsublemma
   
    proof = ≤∧≢⇒< sublemma≤ sublemma≢

*<-lemma2 : {n m x y : ℕ} → x < n → y < m → y + x * m < n * m
*<-lemma2 {n} {m} {x} {y} x<n y<m = y+x*m<n*m
  where
    1+x≤n : 1 + x ≤ n
    1+x≤n = x<n
    
    y+x*m<n*m : y + x * m < n * m
    y+x*m<n*m = begin-strict
      y + x * m     <⟨ +-mono-<-≤ y<m ≤-refl ⟩
      m + x * m     ≡⟨ refl ⟩
      (1 + x) * m   ≤⟨ *-mono-≤ 1+x≤n ≤-refl ⟩
      n * m         ∎
      where
        open ≤-Reasoning
        
sub≤-lemma0 : (x y : ℕ) → y - x ≤ y
sub≤-lemma0 0 y = ≤-refl
sub≤-lemma0 (suc x) 0 = z≤n
sub≤-lemma0 (suc x) (suc y) = begin
  y - x  ≤⟨ sub≤-lemma0 x y ⟩ 
  y      ≤⟨ n≤1+n y ⟩
  1 + y  ∎
  where
    open ≤-Reasoning


sub≤-lemma : {x₁ x₂ y : ℕ} → x₁ ≤ y → x₂ ≤ y → y - x₁ ≡ y - x₂ → x₁ ≡ x₂
sub≤-lemma {0} {0} {_} _ _ _ = refl
sub≤-lemma {suc x₁} {_} {0} ()
sub≤-lemma {_} {suc x₂} {0} _ ()
sub≤-lemma {suc x₁} {0} {suc y} (s≤s x₁≤y) z≤n y-x₁≡1+y = ⊥-elim contradiction
  where
    y-x₁<1+y : y - x₁ < 1 + y
    y-x₁<1+y = begin-strict
      y - x₁  ≤⟨ sub≤-lemma0 x₁ y ⟩
      y       <⟨ n<1+n y ⟩
      1 + y   ∎
      where
        open ≤-Reasoning

    y-x₁≢1+y : y - x₁ ≢ 1 + y
    y-x₁≢1+y = ≢-sym (>⇒≢ y-x₁<1+y)

    contradiction = y-x₁≢1+y y-x₁≡1+y
sub≤-lemma {0} {suc x₂} {suc y} z≤n (s≤s x₂≤y) 1+y≡y-x₂ = ⊥-elim contradiction
  where
    y-x₂<1+y : y - x₂ < 1 + y
    y-x₂<1+y = begin-strict
      y - x₂  ≤⟨ sub≤-lemma0 x₂ y ⟩
      y       <⟨ n<1+n y ⟩
      1 + y    ∎
      where
        open ≤-Reasoning

    1+y≢y-x₂ : 1 + y ≢ y - x₂
    1+y≢y-x₂ = >⇒≢ y-x₂<1+y
    
    contradiction  = 1+y≢y-x₂ 1+y≡y-x₂
sub≤-lemma {suc x₁} {suc x₂} {suc y} (s≤s x₁≤y) (s≤s x₂≤y) hyp = cong suc (sub≤-lemma x₁≤y x₂≤y hyp)

