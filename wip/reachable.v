
(* X  Z  given search reachable subset Y *)

(* phase I *)

(* put all ancestors of Z into A *)
   
   Lz = Z as seq 
   A = [::] // compute ancestors of Z 
   while Lz != [::] 
   ( Lz = Lz - z 
     if z \notin A then  Lz = Lz U Pa(z) end
     A = A u {y} )
   
   L = {(X,Up)}
   V = [::] (collect visited (node,dir)
   R = [::] (collect the reachables via active) 

   while L != [::] 
   Nd= get L head (y,d) 
   L = L \ (y,d)
   si (y,d) non dans V alors
     si y non dans W then
        R = R u {y}
     end 
     V = V u {(y,d)}
     if d = up and y \not in W alors 
        forall py \in Pa(y)
          L= L u {(py,up)}
        forall cy \in child(y)
          L= L u {(cy,down)}
     elseif d = down then 
        if y not in W then 
          foall cy \in Ch(Y) L = L u (cy,down) end 
        end 
        if Y in A then 
          forall py \in Pa(y) L = L U {(py,up)}
        end 
  Return R.
        

   
