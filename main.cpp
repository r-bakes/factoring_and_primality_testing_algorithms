#include <iostream>
#include <vector>
#include <map>
#include <cmath>
#include <algorithm>

unsigned long long int
gcd(unsigned long long int a,
    unsigned long long int b)
// Finds the greatest common divisor of a and b using the euclidean algorithm.
{
 if (b==0)
     return a;
 return gcd(b, a%b);
}

std::map<unsigned long long int, long long int>
extended_euclidean(unsigned long long int a,
                   unsigned long long int b)
// Computes quadratic inverse of a mod b via relation
// gcd(a,b) = 1 = x*a + y*b.
{
    std::map<unsigned long long int, long long int> coefficients;
    long long int x0, x1, y0, y1;
    x0 = 1, x1 = 0, y0 = 0, y1 = 1;

    unsigned long long int a0 = a;
    unsigned long long int b0 = b;

    while(b)
    {
        auto m = floor(a/b);
        auto x2 = x1; // temp store
        x1 = x0 - m*x1;
        x0 = x2;

        auto y2 = y1; // temp store
        y1 = y0 - m*y1;
        y0 = y2;

        auto b1 = b; // temp store
        auto a1 = a;
        a = b1;
        b = a1%b;
    }

    coefficients[a0] = x0;
    coefficients[b0] = y0;

    return coefficients;
}

unsigned long long int
mod_expo(unsigned long long int a,
         unsigned long long int b,
         unsigned long long int m)
// Computes a^b MOD m for b >= O.
{
    unsigned long long int n = 1;
    while (b != 0)
    {
        if (b % 2 == 1)
        {
            n = (n * a) % m;
        }
        b = floor(b/2);
        a = (a * a) % m;
    }
    return n;
}

std::pair<std::vector<unsigned long long int>, unsigned long long int>
modified_trial_division(unsigned long long int n,
                        std::vector<unsigned long long int> P)
// Given int n and list of primes P finds n = p1^a1 * p2^a2 * ... * s.
{

    std::vector<unsigned long long int> factors(P.size());    // map represents--prime factor : power

    for(unsigned long long int i=0; i<P.size(); i++)
    {
        while (n % P[i] == 0)
        {
            n = n/P[i];
            factors[i] = factors[i] + 1;
        }
    }
    return std::make_pair(factors, n);
}

bool strong_pseudoprime_test(unsigned long long int n, int base_max, bool suppress_output = true)
// Strong pseudoprime test for primaility testing. Tests integers b up to base_max for all b where n, b coprime.
{
    int bases_attempted = 0;
    if(n>2 and n % 2 == 0)
        return false;

    for (int b=2; b<=base_max; ++b)
    {
        bool passed = false;
        if (gcd(n, b) != 1)
            continue; // n must be coprime to base b

        ++bases_attempted;
        auto t = n - 1;
        auto a = 0;

        while (t % 2 == 0)
        {
            t = t/2;
            ++a;
        }

        auto factor = mod_expo(b, t, n);

        if (factor == 1 or factor == n - 1)
            passed = true;

        else
        {

            for (int i = 1; i <= a - 1; ++i)
            {
                factor = (factor * factor) % n;

                if (factor == n - 1)
                    passed = true;

            }
        }

        if (passed)
            continue;

        else{
            if(!suppress_output)
                std::cout << n << " is not prime--failed for base " << b << " (a prime p is a base b pseudoprime for all b)\n";
            return false;
        }
    }
    if(!suppress_output)
        std::cout << n << " is likely prime--tested for " << bases_attempted << " bases less then " << base_max << "\n";
    return true; // all bases passed
}

short int
jacobi_symbol(unsigned long long int n, unsigned long long int p)
// Given an integer n and an odd prime p, this algorithm computes the Jacobi symbol (n/p).
// When p is prime, this provides the legendre symbol.
// Originally implemented books version but having issues, so below similar to instructors implementation
{
    n = n % p;
    short int jacobi = 1;
    while( n != 0 )
    {
        while(n % 2 == 0)
        {
            n = n / 2;
            auto criteria1 = p % 8;
            if(criteria1 == 3 or criteria1 == 5)
                jacobi = -1 * jacobi;

        }
        auto swap_n = n;
        n = p, p = swap_n;

        if(n % 4 == 3 and p % 4 == 3)
            jacobi = -1 * jacobi;
        n = n % p;
    }
    if(p == 1)
        return jacobi;
    else
        return 0;
}

unsigned long long int
tonelli(unsigned long long int a, unsigned long long int p, bool output_suppress = true)
{
    if (jacobi_symbol(a,p) != 1)
    {
        std::cout << "Not a square!";
        return 0;
    }

    // Pull twos
    unsigned long long int s = 0;
    auto t = p-1;

    while(t % 2 == 0)
    {
        t = floor(t/2);
        s++;
    }
//    std::cout << p-1 << " = 2^" << s << "*" << t << std::endl;

    // Get a non residue
    unsigned long long int b;
    for(unsigned long long int i=0; i<p; i++)
    {
        if(jacobi_symbol(i, p) == -1)
            b = i;
    }
//    std::cout << "Non-residue b = " << b << std::endl;

    auto inverses = extended_euclidean(b, p);
    auto inverse = inverses[b];

    // Find i so that (a/b^i)^t = 1 mod p
    std::vector<unsigned long long int> i = {0, 2};

    for(int j = 2; j < s+1; j++) {
        if (mod_expo(a * mod_expo(inverse, i[j - 1], p), t * (pow(2, (s - j))), p) == 1)
            i.push_back(i[j - 1]);

        else
            i.push_back(i[j - 1] + pow(2, (j - 1)));
    }

    auto sqrt = mod_expo(b, i[i.size()-1]/2, p) * mod_expo(a*mod_expo(inverse, i[i.size()-1], p), (t+1)/2, p) % p;

    // report for question 2
    if(!output_suppress) {
        std::cout << "i_k: ";
        for (std::vector<unsigned long long int>::const_iterator k = i.begin(); k != i.end(); ++k)
            std::cout << *k << ' ';
    }

    return sqrt;
}

std::vector<std::vector<unsigned long long int>>
rref(std::vector<std::vector<unsigned long long int>> matrix)
{
    std::vector<std::vector<unsigned long long int>> m = matrix;
    unsigned long long int x_dim, i_current, y_dim, j_current;
    x_dim = m[0].size(), j_current = 0, y_dim = m.size(), i_current = 0;

    unsigned long long int i_pivot;
    bool update;
    while(i_current < y_dim and j_current < x_dim)
    {
        i_pivot = i_current;
        update = false;
        while(i_pivot < y_dim)
        {
            if (m[i_pivot][j_current] == 1) // Pivot row index found
            {
                if (i_pivot - i_current >= 1) // Swap rows
                {
                    auto row_store_for_swap = m[i_current];
                    m[i_current] = m[i_pivot];
                    m[i_pivot] = row_store_for_swap;
                    i_pivot = i_current;
                }


                for (auto i = 0; i < y_dim; i++) // Zero jth cols for rows above and below the current pivot row
                {
                    if (m[i][j_current] == 1 and i != i_pivot)
                    {
                        for (unsigned long long int j = 0; j < x_dim; j++)
                        {
                            m[i][j] = (m[i][j] + m[i_pivot][j]) % 2;
                        }
                    }
                }
                i_current++;
                j_current++;
                update = true;
                break;
            }
            i_pivot++;
        }
        if(!update)
            j_current++; // zero column
    }
    return m;
}

std::vector<std::vector<unsigned long long int>>
solution_basis(std::vector<std::vector<unsigned long long int>> m)
{
    std::vector<std::vector<unsigned long long int>> basis;
    std::vector<unsigned long long int> free_variables_col;

    // determine free variables
    unsigned long long int x_dim, y_dim, j_prev;
    x_dim = m[0].size(), y_dim = m.size();

//    free_variables.push_back();

//    unsigned long long int i,j;
//    i = 0;

    // find column of first pivot point (in first row)
    for(unsigned long long int j0 = 0; j0 < y_dim; j0++)
    {
        if(m[0][j0] == 1)
            j_prev = j0;

    }

    for(unsigned long long int i = 1; i < y_dim; i++) // catch intermediate free variables
    {
        for(unsigned long long int j = j_prev+1; j<x_dim; j++)
        {
            if(m[i][j] == 1)
            {
                if(j-j_prev>1)
                {
                    for(unsigned long long int j_free = j_prev+1; j_free < j; j_free++)
                        free_variables_col.push_back(j_free);
                }
                j_prev = j;
                break;
            }
        }
    }
    for(unsigned long long int j_free = j_prev+1; j_free < x_dim; j_free++) // add trailing free variable columns
        free_variables_col.push_back(j_free);

    // iterate over free variables, plug in 1 for column, solve for pivot variables.
    for(unsigned long long int var_i = 0; var_i < free_variables_col.size(); var_i++)
    {
        std::vector<unsigned long long int> coefficients(m[0].size());
        coefficients[free_variables_col[var_i]] = 1;

        // iterate down free variable column and find rows not equal to 0
        for(unsigned long long int y = 0; y < m.size(); y++)
        {
            if(m[y][free_variables_col[var_i]] != 0)
            {
                for(unsigned long long int x_free = 0; x_free < x_dim; x_free++)
                {
                    if(m[y][x_free] == 1)
                    {
                        coefficients[x_free] = 1;
                        break;
                    }
                }
            }
        }
        basis.push_back(coefficients);
    }

    return basis;

}

std::vector<unsigned long long int>
prime_list(unsigned long long int B)
{
    // Returns a list of prime factors < B using the strong pseudoprime test
    std::vector<unsigned long long int> primes;
    for(unsigned long long int i = 2; i < B; i++)
    {
        if(strong_pseudoprime_test(i, 50))
            primes.push_back(i);
    }
    return primes;
}

std::vector<unsigned long long int>
factor_base(unsigned long long int n, std::vector<unsigned long long int> P)
{
    // Returns a list of base factors such that (n/p)=1 (Jacobi Symbol).
    std::vector<unsigned long long int> bases;
    for(unsigned long long int p : P)
    {
        if(jacobi_symbol(n, p) == 1)
            bases.push_back(p);
    }
    return bases;
}

std::vector<unsigned long long int>
quadratic_sieve(unsigned long long int n, unsigned long int B, unsigned long int M)
{
    std::vector<unsigned long long int> factors;
    std::vector<unsigned long long int> R;
    std::vector<unsigned long long int> F;
    std::vector<long double> H;
    for(long double r = floor(sqrt(n))+1; r < floor(sqrt(n))+1+M; r++)
    {
        auto f = pow(r,2)-n;
        R.push_back(r);
        F.push_back(f);
        H.push_back(log(f));
    }

    std::vector<unsigned long long int> residues;
    std::vector<unsigned long long int> bases = factor_base(n, prime_list(B));
    for(unsigned long long int b : bases)
    {
        if(b==2) // exception of prime p == 2 (tonelli's not catching this--always reports 0 for sqrt...)
        {
            if(n % 2 == 1)
                residues.push_back(1);
            else
                residues.push_back(0);
        }
        else
            residues.push_back(tonelli(n, b));
    }

    // report for 5 c)
    std::cout << std::endl << "   Bases: ";
    for(auto base : bases)
        std::cout << base << " ";
    std::cout << std::endl << "Residues: ";
    for(auto r : residues)
        std::cout << r << " ";

    for(auto p : bases)
    {
        for(unsigned long long int i = 0; i < R.size(); i++)
        {
            if(F[i] % p == 0)
                H[i] = H[i] - log(p);
        }

    }

    std::vector<std::vector<unsigned long long int>> matrix;
    std::vector<unsigned long long int> b_smooth_r;
    for(unsigned long long int i = 0; i < R.size(); i++)
    {
        if(abs(H[i]) <= 4) // "close to zero |"
        {
            unsigned long long int power = (unsigned long long int)(pow(R[i], 2));
            auto result = modified_trial_division(power % n, bases);
            if(result.second == 1)
            {
                matrix.push_back(result.first);
                b_smooth_r.push_back(R[i]);
            }
        }
    }
    auto exponents_store = matrix;

    // reporting for 5 f)
    std::cout << std::endl << "\n\n" << "B smooth r: " << b_smooth_r.size() << " found vs. " << bases.size() << " primes in basis." << std::endl;
    for(unsigned long long int i=0; i < b_smooth_r.size(); i++)
    {
        std::cout << std::endl << b_smooth_r[i] << " | " ;
        for(unsigned long long int j=0; j<matrix[i].size(); j++)
        {
            std::cout << bases[j] << "^" << matrix[i][j] << " ";
        }
    }

    // Transpose matrix and reduce elements mod 2
    std::vector<std::vector<unsigned long long int>> matrix_final(matrix[0].size());

    for(unsigned long long int j = 0; j < matrix[0].size(); j++)
    {
        std::vector<unsigned long long int> row(matrix.size());
        for(unsigned long long int i = 0; i < matrix.size(); i++)
            row[i] = matrix[i][j] % 2;
        matrix_final[j] = row ;
    }

    // row reduce final matrix
    matrix = rref(matrix_final);

    // output rref basis
    auto soln_basis = solution_basis(matrix);

    std::vector<unsigned long long int> X;
    std::vector<unsigned long long int> Y;
    for(unsigned long long int i = 0; i < soln_basis.size(); i++)
    {
        unsigned long long int y, x;
        y=1, x=1;
        std::vector<unsigned long long int> exponent_vector(bases.size());
        auto soln = soln_basis[i];
        for(unsigned long long int j = 0; j < soln.size(); j++)
        {
            if(soln[j] == 1)
            {
                x = (x * b_smooth_r[j]) % n;
                for(unsigned long long int k=0; k < exponents_store[0].size(); k++)
                    exponent_vector[k] = exponent_vector[k] + exponents_store[j][k];
            }
        }

        for(unsigned long long int j = 0; j < exponent_vector.size(); j++)
            y = (y * (unsigned long long int)pow(bases[j], exponent_vector[j]/2)) % n;

        X.push_back(x), Y.push_back(y);
        unsigned long long int difference;
        if(y > x)
            difference = y-x;
        else
            difference = x-y;
        auto potential_factor = gcd(difference, n);
        if(potential_factor != n and potential_factor > 1) // FACTOR FOUND!
            if (std::find(factors.begin(), factors.end(), potential_factor) != factors.end()) // check if already found
                continue;
            else
                factors.push_back(potential_factor); // New Factor Found
    }

    std::cout << "\n\nx | y | x^2 mod n | y^2 mod n " << std::endl;
    for(unsigned long long int i=0; i<X.size(); i++)
    {
        std::cout << X[i] << " | " << Y[i] << " | " <<  (unsigned long long int)pow(X[i], 2) % n <<  " | " << (unsigned long long int)pow(Y[i], 2) % n << std::endl;
    }

    return factors;
}

int main()
{
    // Quadratic Sieve Demo
    std::cout << "\n\n" << "Quadratic Sieve Demo " << std::endl;
    unsigned long long int num = 20304569;
    std::cout << "\n\n" << "Factoring: " <<  num << std::endl;

    // check if number is prime
    auto primality = strong_pseudoprime_test(num, 100, false);

    if (! primality)
    {
            auto factors = quadratic_sieve(num, 1000, 500);
            std::cout << "\n\nFactors: " << std::endl;
            for (unsigned long long int i = 0; i < factors.size(); i++)
            {
                num = num / factors[i];
                std::cout << factors[i] << " ";
            }
            std::cout << num << std::endl;
    }
}