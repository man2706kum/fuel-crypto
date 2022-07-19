#include<stdio.h>

typedef unsigned long long limb_t;
typedef unsigned long llimb_t;
int LIMB_T_BITS  = 32;


void mul_mont_n(limb_t ret[], const limb_t a[], const limb_t b[], const limb_t p[], limb_t n0, int n)
{
    llimb_t limbx;
    limb_t mask, borrow, mx, hi, tmp[n+1], carry;
    int i, j;

    for (mx=b[0], hi=0, i=0; i<n; i++) {
        limbx = (mx * (llimb_t)a[i]) + hi;
        tmp[i] = (limb_t)limbx;
        hi = (limb_t)(limbx >> LIMB_T_BITS);
    }
    mx = n0*tmp[0];
    tmp[i] = hi;

    for (carry=0, j=0; ; ) {
        limbx = (mx * (llimb_t)p[0]) + tmp[0];
        hi = (limb_t)(limbx >> LIMB_T_BITS);
        for (i=1; i<n; i++) {
            limbx = (mx * (llimb_t)p[i] + hi) + tmp[i];
            tmp[i-1] = (limb_t)limbx;
            hi = (limb_t)(limbx >> LIMB_T_BITS);
        }
        limbx = tmp[i] + (hi + (llimb_t)carry);
        tmp[i-1] = (limb_t)limbx;
        carry = (limb_t)(limbx >> LIMB_T_BITS);

        if (++j==n)
            break;

        for (mx=b[j], hi=0, i=0; i<n; i++) {
            limbx = (mx * (llimb_t)a[i] + hi) + tmp[i];
            tmp[i] = (limb_t)limbx;
            hi = (limb_t)(limbx >> LIMB_T_BITS);
        }
        mx = n0*tmp[0];
        limbx = hi + (llimb_t)carry;
        tmp[i] = (limb_t)limbx;
        carry = (limb_t)(limbx >> LIMB_T_BITS);
    }

    for (borrow=0, i=0; i<n; i++) {
        limbx = tmp[i] - (p[i] + (llimb_t)borrow);
        ret[i] = (limb_t)limbx;
        borrow = (limb_t)(limbx >> LIMB_T_BITS) & 1;
    }

    mask = carry - borrow;

    for(i=0; i<n; i++)
        ret[i] = (ret[i] & ~mask) | (tmp[i] & mask);
}

void redc_mont_n(limb_t ret[], const limb_t a[], const limb_t p[], limb_t n0, int n)
{
    llimb_t limbx;
    limb_t mask, carry, borrow, mx, hi, tmp[n];
    const limb_t *b = a;
    int i, j;

    for (j=0; j<n; j++) {
        mx = n0*b[0];
        limbx = (mx * (llimb_t)p[0]) + b[0];
        hi = (limb_t)(limbx >> LIMB_T_BITS);
        for (i=1; i<n; i++) {
            limbx = (mx * (llimb_t)p[i] + hi) + b[i];
            tmp[i-1] = (limb_t)limbx;
            hi = (limb_t)(limbx >> LIMB_T_BITS);
        }
        tmp[i-1] = hi;
        b = tmp;
    }

    for (carry=0, i=0; i<n; i++) {
        limbx = a[n+i] + (tmp[i] + (llimb_t)carry);
        tmp[i] = (limb_t)limbx;
        carry = (limb_t)(limbx >> LIMB_T_BITS);
    }

    for (borrow=0, i=0; i<n; i++) {
        limbx = tmp[i] - (p[i] + (llimb_t)borrow);
        ret[i] = (limb_t)limbx;
        borrow = (limb_t)(limbx >> LIMB_T_BITS) & 1;
    }

    mask = carry - borrow;

    for(i=0; i<n; i++)
        ret[i] = (ret[i] & ~mask) | (tmp[i] & mask);
}


int main() {
    limb_t res[6], b[6] ={0,0,0,0,0,1}, a[6] ={0,0,0,0,0,1}, p[6] = {0xb9feffffffffaaab, 0x1eabfffeb153ffff, 0x6730d2a0f6b0f624, 0x64774b84f38512bf, 0x4b1ba7b6434bacd7, 0x1a0111ea397fe69a}; //a[6] = {0xb9feffffffffaaab,0x1eabfffeb153ffff,0x6730d2a0f6b0f624,0x64774b84f38512bf,0x4b1ba7b6434bacd7,0x1a0111ea397fe69a}, b[6] ={1,0,0,0,0,0}, p[6] = {0xb9feffffffffaaab, 0x1eabfffeb153ffff, 0x6730d2a0f6b0f624, 0x64774b84f38512bf, 0x4b1ba7b6434bacd7, 0x1a0111ea397fe69a};

    // mul_mont_n(res, a, b, p, 0x89f3fffcfffcfffd, 6);
    // for (int i = 0; i < 6; i++)
    // {
    //     printf("%llu \n", res[i]);
    // }

    // limb_t aa[12] = {0xb9feffffffffaaab, 0x1eabfffeb153ffff, 0x6730d2a0f6b0f624, 0x64774b84f38512bf, 0x4b1ba7b6434bacd7, 0x1a0111ea397fe69a,0,0,0,0,0,0};
    // redc_mont_n(res, aa, p, 0x89f3fffcfffcfffd, 6);
    // for (int i = 0; i < 6; i++)
    // {
    //     printf("%llu \n", res[i]);
    // }

    limb_t aa[12] = {13282407956253574712,7557322358563246340,14991082624209354397,6631139461101160670,10719928016004921607,1730705806359781376,0,0,0,0,0,0};
    redc_mont_n(res, aa, p, 0x89f3fffcfffcfffd, 6);
    for (int i = 0; i < 6; i++)
    {
        printf("%llu \n", res[i]);
    }
}
