module Util.BinN where

open import Basic
open import Data.Vec using (_β·_)
open import Relation.Binary.PropositionalEquality as PropEq
open import Util.Arithmetic
open import Util.List
open import Util.List.Properties

π^ : (n : β) β List (Vec Bool n)
π^ 0 = [] β· []
π^ (suc n) = (map (_β·_ true) (π^ n)) ++ (map (_β·_ false) (π^ n))

|π^n|β‘2^n : (n : β) β length (π^ n) β‘ 2 ^ n
|π^n|β‘2^n 0 = refl
|π^n|β‘2^n (suc n) = 
  length (π^ (1 + n))
  
      β‘β¨ refl β©
      
  length ((map (_β·_ true) (π^ n)) ++ (map (_β·_ false) (π^ n)))
  
      β‘β¨ length-++ (map (_β·_ true) (π^ n)) β©
      
  length (map (_β·_ true) (π^ n)) + length (map (_β·_ false) (π^ n))
  
      β‘β¨ cong (Ξ» y β y + length (map (Data.Vec._β·_ false) (π^ n))) (length-map (_β·_ true) (π^ n)) β©
      
  length (π^ n) + length ((map (_β·_ false) (π^ n)))
  
      β‘β¨ cong (Ξ» y β length (π^ n) + y) (length-map (_β·_ false) (π^ n)) β©
      
  length (π^ n) + length (π^ n)
  
      β‘β¨ x+xβ‘2x (length (π^ n)) β©
      
  2 * (length (π^ n))
  
      β‘β¨ cong (Ξ» y β 2 * y) ind β©
      
  2 * (2 ^ n)
  
      β‘β¨ refl β©
      
  2 ^ (1 + n)
  
      β
    where
      open PropEq.β‘-Reasoning

      ind : length (π^ n) β‘ 2 ^ n
      ind = |π^n|β‘2^n n


π^n-complete : {n : β} β (v : Vec Bool n) β Ξ£[ i β β ] (Ξ£[ i<|l| β i < length (π^ n) ] (lookup< (π^ n) i i<|l|) β‘ v)
π^n-complete {0} [] = 0 , ((sβ€s zβ€n) , refl)
π^n-complete {suc n} v@(true β· xs) = i , (i<|π^1+n| , π^1+n[i]β‘v)
  where
    ind : Ξ£[ i' β β ] (Ξ£[ i'<|π^n| β i' < length (π^ n) ] (lookup< (π^ n) i' i'<|π^n|) β‘ xs)
    ind = π^n-complete xs
    i' = projβ ind
    i'<|π^n| = projβ (projβ ind)
    π^n[i']β‘xs = projβ (projβ ind)

    i'<|map-t-π^n| : i' < length (map (_β·_ true) (π^ n))
    i'<|map-t-π^n| = (index-map-lemma (π^ n) i' i'<|π^n| (_β·_ true))
    
    map-t-π^n[i']β‘tβ·π^n[i'] : lookup< (map (_β·_ true) (π^ n)) i' i'<|map-t-π^n| β‘ (true β· (lookup< (π^ n) i' i'<|π^n|))
    map-t-π^n[i']β‘tβ·π^n[i'] = lookup<-map-lemma (π^ n) i' i'<|π^n| (_β·_ true)

    tβ·π^n[i']β‘v : (true β· (lookup< (π^ n) i' i'<|π^n|)) β‘ v
    tβ·π^n[i']β‘v = cong (_β·_ true) π^n[i']β‘xs

    map-t-π^n[i']β‘v : lookup< (map (_β·_ true) (π^ n)) i' i'<|map-t-π^n| β‘ v
    map-t-π^n[i']β‘v = β‘-trans map-t-π^n[i']β‘tβ·π^n[i'] tβ·π^n[i']β‘v

    i'<|π^1+n| : i' < length (π^ (1 + n))
    i'<|π^1+n| = index-++-lemmaβ (map (_β·_ true) (π^ n)) (map (_β·_ false) (π^ n)) i' i'<|map-t-π^n|

    map-t-π^n[i']β‘π^1+n[i'] : lookup< (map (_β·_ true) (π^ n)) i' i'<|map-t-π^n| β‘ lookup< (π^ (1 + n)) i' i'<|π^1+n|
    map-t-π^n[i']β‘π^1+n[i'] = lookup<-++-lemmaβ (map (_β·_ true) (π^ n)) (map (_β·_ false) (π^ n)) i' i'<|map-t-π^n|
    
    i = i'
    i<|π^1+n| = i'<|π^1+n|
    
    π^1+n[i]β‘v = β‘-trans (β‘-sym map-t-π^n[i']β‘π^1+n[i']) map-t-π^n[i']β‘v
    
π^n-complete {suc n} v@(false β· xs) = i , (i<|π^1+n| , π^1+n[i]β‘v)
  where
    ind : Ξ£[ i' β β ] (Ξ£[ i'<|π^n| β i' < length (π^ n) ] (lookup< (π^ n) i' i'<|π^n|) β‘ xs)
    ind = π^n-complete xs
    
    i' = projβ ind
    i'<|π^n| = projβ (projβ ind)
    π^n[i']β‘xs = projβ (projβ ind)

    i'<|map-f-π^n| : i' < length (map (_β·_ false) (π^ n))
    i'<|map-f-π^n| = (index-map-lemma (π^ n) i' i'<|π^n| (_β·_ false))
    
    map-f-π^n[i']β‘fβ·π^n[i'] : lookup< (map (_β·_ false) (π^ n)) i' i'<|map-f-π^n| β‘ (false β· (lookup< (π^ n) i' i'<|π^n|))
    map-f-π^n[i']β‘fβ·π^n[i'] = lookup<-map-lemma (π^ n) i' i'<|π^n| (_β·_ false)

    fβ·π^n[i']β‘v : (false β· (lookup< (π^ n) i' i'<|π^n|)) β‘ v
    fβ·π^n[i']β‘v = cong (_β·_ false) π^n[i']β‘xs

    map-f-π^n[i']β‘v : lookup< (map (_β·_ false) (π^ n)) i' i'<|map-f-π^n| β‘ v
    map-f-π^n[i']β‘v = β‘-trans map-f-π^n[i']β‘fβ·π^n[i'] fβ·π^n[i']β‘v
    
    i = length (map (_β·_ true) (π^ n)) + i'
    
    i<|π^1+n| : i < length (π^ (1 + n))
    i<|π^1+n| = index-++-lemmaβ (map (_β·_ true) (π^ n)) (map (_β·_ false) (π^ n)) i' i'<|map-f-π^n|

    map-f-π^n[i']β‘π^1+n[i] : lookup< (map (_β·_ false) (π^ n)) i' i'<|map-f-π^n| β‘ lookup< (π^ (1 + n)) i i<|π^1+n|
    map-f-π^n[i']β‘π^1+n[i] = lookup<-++-lemmaβ (map (_β·_ true) (π^ n)) (map (_β·_ false) (π^ n)) i' i'<|map-f-π^n|

    π^1+n[i]β‘v = β‘-trans (β‘-sym map-f-π^n[i']β‘π^1+n[i]) map-f-π^n[i']β‘v
