# Function for benchmarking
MicroSeconds := function()
  local t;
  t := CurrentTime();
  return t.tv_sec * 1000000 + t.tv_usec;
end;
Bench := function(f,G,N)
  local tstart, tend;
  tstart := MicroSeconds();
  f(G,N);
  tend := MicroSeconds();
  return (tend-tstart) * 1.0 / 1000000;
end;

# Create free group
f := FreeGroup("a","b");

# Create list of groups
T := [];

# 1 Triangle group (2,3,7)
Add(T, f / [f.1^2, f.2^3, (f.1*f.2)^7]);

# 2 Hecke group H_5
Add(T, f / [f.1^2, f.2^5]);

# 3 Symmetric group S_6
Add(T, f / [f.1^2, f.2^5, (f.1*f.2)^6, Comm(f.1,f.2)^3, Comm(f.1,f.2*f.1*f.2)^2]);

# 4 Alternating group A_6
Add(T, f / [f.1^2, f.2^4, (f.1*f.2)^5, (f.1*f.2^2)^5]);

# 5 Linear group L_2(7) = L_3(2)
Add(T, f / [f.1^2, f.2^3, (f.1*f.2)^7, Comm(f.1,f.2)^4]);

# 6 Linear group L_3(5)
Add(T, f / [f.1^3, f.2^5, f.1*f.2*f.1^-1*f.2*f.1*f.2*f.1^-1*f.2^2*f.1*f.2^-2*f.1^-1*f.2^2, f.1*f.2*f.1*f.2^-2*(f.1^-1*f.2^2*f.1^-1*f.2^-2)^3]);

# 7 Unitary group U_4(2) = S_4(3)
Add(T, f / [f.1^2, f.2^5, (f.1*f.2)^9, Comm(f.1, f.2)^3, Comm(f.1, f.2*f.1*f.2)^2]);

# 8 Sympleptic group S_10(2)
Add(T, f / [f.1^2, f.2^11, (f.1*f.2)^15, (f.1*f.2^5)^18, Comm(f.1, f.2)^3, Comm(f.1, f.2^2)^2, Comm(f.1, f.2^3)^2, Comm(f.1, f.2^4)^2, Comm(f.1, f.2^5)^3, Comm(f.1, (f.1*f.2)^5)^2]);

# 9 Orthogonal group O_8+(2)
Add(T, f / [f.1^2, f.2^10, Comm(f.1,f.2)^2, Comm(f.1,f.2^2)^2, Comm(f.1,f.2^5)^4, Comm(f.1,f.2^3)^3, Comm(f.1,f.2^4)^3, (f.1*f.2^3*f.1*f.2^4)^7]);

# 10 Held group He
Add(T, f / [f.1^2, f.2^7, (f.1*f.2)^17, Comm(f.1,f.2)^6, Comm(f.1,f.2^3)^5, Comm(f.1,f.2*f.1*f.2*f.1*f.2^-1*f.1*f.2*f.1*f.2), (f.1*f.2)^4*f.1*f.2^2*f.1*f.2^-3*f.1*f.2*f.1*f.2*f.1*f.2^-1*f.1*f.2^3*f.1*f.2^-2*f.1*f.2^2]);

# 11 Mathieu group M_12
Add(T, f / [f.1^2, f.2^3, (f.1*f.2)^11, Comm(f.1,f.2)^6, (f.1*f.2*f.1*f.2*f.1*f.2^-1)^6]);

# 12 Conway group Co_2
Add(T, f / [f.1^2, f.2^5, (f.1*f.2^2)^9, Comm(f.1, f.2)^4, Comm(f.1, f.2^2)^4, Comm(f.1, f.2*f.1*f.2)^3, Comm(f.1, f.2*f.1*f.2^2*f.1*f.2)^2, Comm(f.1, f.2*f.1*f.2^-2)^3, Comm(f.1, f.2^-2*f.1*f.2*f.1*f.2^-2)^2, (f.1*f.2*f.1*f.2^2*f.1*f.2^-1*f.1*f.2^-2)^7]);

# 13 Janko group J_3
Add(T, f / [f.1^2, f.2^3, (f.1*f.2)^19, Comm(f.1, f.2)^9, ((f.1*f.2)^6*(f.1*f.2^-1)^5)^2, ((f.1*f.2*f.1*f.2*f.1*f.2^-1)^2*f.1*f.2*f.1*f.2^-1*f.1*f.2^-1*f.1*f.2*f.1*f.2^-1)^2, f.1*f.2*f.1*f.2*(f.1*f.2*f.1*f.2^-1)^3*f.1*f.2*f.1*f.2*(f.1*f.2*f.1*f.2^-1)^4*f.1*f.2^-1*(f.1*f.2*f.1*f.2^-1)^3, (f.1*f.2*f.1*f.2*f.1*f.2*f.1*f.2*f.1*f.2^-1*f.1*f.2*f.1*f.2^-1)^4]);

# 14 Alternating group A_5
Add(T, f / [f.1^2, f.2^3, (f.1*f.2)^5]);