#include <stdio.h>

power(int base, int exp) {

	while (exp != 0) {
		base *= base;
		--exp;
	}
	return base
}

zeta(int s, int n) {
	
	for (int i = 0; i < n; ++i) {
		res += 1 / power(i, s);
	}
	return  
}


int main()
{
	printf("n = %d,  Zeta(2) = ", n, zeta(2)")	
}
