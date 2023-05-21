# To get the Julia repl running, press <Shift + Enter>

#print(BigFloat(2.1));
using LinearAlgebra


x = Int32(10);

#define the matrix function
function matrix_fun(i,j)
    if (i==j) 
        BigFloat(3.0)
    elseif (i - j == 1)
        BigFloat(-1.0)
    elseif (j - i == 1)
        BigFloat(-1.0)
    else
        BigFloat(0.0)
    end
end


# Define a matrix
function matrix()
    array = Array{BigFloat}(undef, x, x);
    for i = 1:x
        for j = 1: x
            array[i,j] = matrix_fun(i,j);
        end
    end
    return array
end

A = matrix();
display(A)



#Using the tridiagonal type from Julia

#create a Vector
function vector_fun(entry, dim)
    vec = Vector{BigFloat}(undef, dim);
    for i = 1: dim
        vec[i] = entry;
    end
    return vec
end


dl = vector_fun(BigFloat(-1.0), x-1); #lower-diagonal vector
du = vector_fun(BigFloat(-1.0), x-1); #upper-diagonal vector
d = vector_fun(BigFloat(3.0), x); #diagonal vector

A_trid = Tridiagonal(dl,d,du);
print("Matrix \n");
display(A_trid)


# righthand side vector
b = vector_fun(BigFloat(1.0), x);
print("Right hand-side vector \n");
display(b)

############### Example from Higham book ########################

#dl = vector_fun(BigFloat(1.0), x-1);
#d = vector_fun(BigFloat(1.5), x);
#A_trid = Bidiagonal(d, dl, :L);
#print("Matrix \n")
#display(A_trid)


#b = vector_fun(BigFloat(2.5), x);
#print("Right hand-side vector \n");
#display(b)

print("Vector norm \t:")
display(norm(b, Inf))
print("\n Matrix norm \t:")
display(opnorm(A, Inf))


tau = BigFloat(1E-06);
display(tau)

# Create a diagonal matrix from a
D = Diagonal(A_trid)
display(D)

D_inv = inv(D);
display(D_inv)

# For double
p = Int32(53);
emax = Int32(1023);
delta = BigFloat(1.0) / BigFloat(2.0 * (BigInt(2)^BigInt(p-1)));
display(delta);

epsilon = BigFloat(1.0) / BigFloat(2.0 * (BigInt(2)^ BigInt(p + emax - 3)));
display(epsilon)


#defining g_epsilon and g_delta
function gdelta(dim)
    return (BigFloat(BigFloat(1.0) + delta)^dim - BigFloat(1.0))
end
display(gdelta(x))

function gepsilon(dim)
    return (BigFloat(1.0 * dim) * epsilon * (BigFloat(1.0) + gdelta(dim-1)))
end
display(gepsilon(x))


# define d_hat
d_hat = (BigFloat(opnorm(D_inv, Inf)) + epsilon) / (BigFloat(1.0) - delta);
display(d_hat)

# Define R
N = A_trid .- D;
display(N)

R = d_hat * BigFloat(opnorm(N, Inf));
display(R)

#define x_bound
x_bound = d_hat * BigFloat(norm(b, Inf)) / BigFloat(BigFloat(1.0) - delta);
display(x_bound)

rho_hat =(((BigFloat(1.0) + gdelta(x)) * (BigFloat(1.0) + delta) * gdelta(x) +
            delta * (BigFloat(1.0) + gdelta(x)) + gdelta(x)) * (1 + delta) + gdelta(x)) * R + R +
        (((BigFloat(1.0)+ gdelta(x)) * (BigFloat(1.0) + delta) * gdelta(x) + 
            delta * (BigFloat(1.0) + gdelta(x)) + gdelta(x)) * epsilon + epsilon) * BigFloat(opnorm(N, Inf)); 
print("rho_hat \n");
display(rho_hat)            
d_hat_mag = (gdelta(x) * (BigFloat(1.0) + delta) + delta) * (d_hat * (BigFloat(1.0)+ delta) + epsilon) * BigFloat(norm(b, Inf)) +
            (BigFloat(1.0)+ gdelta(x)) * gepsilon(x)* (BigFloat(1.0)+ delta) *(d_hat * (BigFloat(1.0)+ delta) + epsilon) +
            gepsilon(x) +
            (d_hat * delta + epsilon) * BigFloat(norm(b, Inf)) +
            (((BigFloat(1.0)+ gdelta(x)) * (BigFloat(1.0) + delta) * gdelta(x) + delta * (BigFloat(1.0) + gdelta(x)) + gdelta(x)) *
                (BigFloat(1.0) + delta) + gdelta(x)) * R +
            ((((BigFloat(1.0)+ gdelta(x)) * (BigFloat(1.0) + delta) * gdelta(x) + delta * (BigFloat(1.0) + gdelta(x)) + gdelta(x)) *
                epsilon + epsilon) * BigFloat(opnorm(N, Inf))) *
                ((d_hat * BigFloat(norm(b, Inf))) / (BigFloat(1.0) - R));
print("d_hat_mag \n")
display(d_hat_mag)
denom = log(BigFloat(1.0)/ BigFloat(rho_hat));
display(denom);


nume = log((x_bound * (BigFloat(1.0) + delta)) / 
    (((sqrt((tau * tau - gepsilon(x)) / (BigFloat(1.0 * x) * (BigFloat(1.0) + gdelta(x)))) - gepsilon(x)) /
    ( (BigFloat(1.0) + gdelta(x)) + BigFloat(opnorm(D, Inf)) * (BigFloat(1.0) + delta))) -
        ((BigFloat(2.0) * d_hat_mag) / (BigFloat(1.0) - rho_hat))));

display(nume)

ceil_aux = BigFloat(nume) / BigFloat(denom);
k_min = BigInt(1) + BigInt(ceil(ceil_aux));
display(k_min)

sol = inv(A)*b;
display(sol)