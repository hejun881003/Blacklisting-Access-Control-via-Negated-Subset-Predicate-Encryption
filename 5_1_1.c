#include <stdio.h> 
#include <stdlib.h> 
#include <stdbool.h>
#include <gmp.h>
#include <pbc/pbc.h>
#include <time.h>

pairing_t pairing;
clock_t start, end;

typedef struct pp{
    element_t p;
    element_t g;
    element_t alpha;
    element_t x[200];
    int n;
} PP;

typedef struct msk{
    element_t msk;
} MSK;

typedef struct mpk{
    element_t X[200];
    element_t Y;
} MPK;

typedef struct sk{
    element_t D0;
    element_t D1;
    element_t K[200];
    element_t r;
} SK;

typedef struct ct{
    element_t U;
    element_t s;
    element_t C0;
    element_t C1;
} CT;


typedef struct set{
    PP pp;
    MSK msk;
    MPK mpk;
} SET;

typedef struct pt{
    element_t msg;
} PT;



SET setup(int n) {
    SET set;
    set.pp.n = n;
    
    element_init_G1(set.pp.g, pairing);
    element_set1(set.pp.g);
    element_init_Zr(set.pp.alpha, pairing);
    element_random(set.pp.alpha);


    for(int i=0; i<=n; i++){
        element_init_Zr(set.pp.x[i], pairing);
        element_random(set.pp.x[i]);
    }
    element_init_G1(set.msk.msk, pairing);
    element_pow_zn(set.msk.msk, set.pp.g, set.pp.alpha);
    for(int i=0; i<=n; i++){
        element_init_G1(set.mpk.X[i], pairing);
        element_pow_zn(set.mpk.X[i], set.pp.g, set.pp.x[i]);
    }
    element_init_GT(set.mpk.Y, pairing);
    element_t egg;
    element_init_GT(egg, pairing);
    element_pairing(egg, set.pp.g, set.pp.g);
    element_pow_zn(set.mpk.Y, egg, set.pp.alpha);

    return set;
}

SK keygen(SET set, element_t Sk_set[], element_t Sk_set_size){
    SK sk;
    element_t r;
    element_t X0_r;
    element_t g_alpha;
    element_t X0_inverse;
    element_init_Zr(r, pairing);
    element_random(r);
    element_init_Zr(sk.r, pairing);
    element_set(sk.r, r);
    element_init_G1(X0_r, pairing);
    element_init_G1(g_alpha, pairing);
    element_init_G1(sk.D0, pairing);
    element_init_G1(sk.D1, pairing);

    element_pow_zn(sk.D0, set.pp.g, r);
    element_pow_zn(g_alpha, set.pp.g, set.pp.alpha);
    element_pow_zn(X0_r, set.mpk.X[0], r);
    element_mul(sk.D1, g_alpha, X0_r);
    mpz_t mpz_val;
    mpz_init(mpz_val);
    int a;
    int b;
    bool arr[200] = {false};
    element_to_mpz(mpz_val, Sk_set_size);
    a = mpz_get_ui(mpz_val);
    for(int i=1; i< a; i++){
        element_to_mpz(mpz_val, Sk_set[i]);
        b = mpz_get_ui(mpz_val);
        arr[b] = true;
    }

    element_init_G1(X0_inverse, pairing);
    element_invert(X0_inverse, set.mpk.X[0]);

    size_t size_of_K;
    size_of_K = element_length_in_bytes(sk.D0) + element_length_in_bytes(sk.D1);

    for(int i=1; i<= set.pp.n; i++){
        element_init_G1(sk.K[i], pairing);
        if(arr[i] == true){
            element_mul(sk.K[i], X0_inverse, set.mpk.X[i]);
            element_pow_zn(sk.K[i], sk.K[i], sk.r);
        }
        else{
            element_pow_zn(sk.K[i], set.mpk.X[i], sk.r);
        }
        size_of_K += element_length_in_bytes(sk.K[i]);
    }

    printf("sk大小: %zu bytes\n", size_of_K);
    return sk;
}

CT encrypt(SET set, element_t M, element_t Sc_set[], element_t Sc_set_size){
    CT ct;
    element_init_Zr(ct.s, pairing);
    element_random(ct.s);
    element_init_GT(ct.U, pairing);
    element_pow_zn(ct.U, set.mpk.Y, ct.s);
    element_mul(ct.U, ct.U, M);

    bool arr[200];
    for (int  i = 0; i < 200; i++){
        arr[i] = true;
    }
    
    mpz_t mpz_val;
    mpz_init(mpz_val);
    element_to_mpz(mpz_val, Sc_set_size);
    int a;
    int b;
    int first_C1_Xi;
    a = mpz_get_ui(mpz_val);
    for(int i=1; i< a; i++){
        element_to_mpz(mpz_val, Sc_set[i]);
        b = mpz_get_ui(mpz_val);
        arr[b] = false;
    }
    element_init_G1(ct.C0, pairing);
    element_pow_zn(ct.C0, set.pp.g, ct.s);
    element_init_G1(ct.C1, pairing);

    for(int i=1; i<=set.pp.n; i++){
        if (arr[i] == true){
            element_set(ct.C1, set.mpk.X[i]);
            first_C1_Xi = i;
            break;
        }
    }

    for(int i = first_C1_Xi; i<= set.pp.n; i++){
        if(arr[i] == true){
            element_mul(ct.C1, set.mpk.X[i], ct.C1);
        }
    }
    element_pow_zn(ct.C1, ct.C1, ct.s);

    return ct;
}

PT decrypt(SET set, CT ct, SK sk, element_t Sc_set[], element_t Sc_set_size, element_t Sk_set[], element_t Sk_set_size){
  
    element_t tmp1;
    element_t tmp2;
    element_t K;
    element_t tmp3;
    element_t tmp4;
    element_t gap_t;
    PT pt;
    element_init_GT(tmp1, pairing);
    element_pairing(tmp1, ct.C0, sk.D1);
    element_init_GT(tmp2, pairing);
    element_init_G1(K, pairing);
    element_init_GT(tmp3, pairing);
    element_pairing(tmp3, ct.C1, sk.D0);
    element_init_GT(tmp4, pairing);
    element_init_GT(pt.msg, pairing);
    element_init_Zr(gap_t, pairing);
  
  
    int a;
    int b;
    int c;
    int first_Ki;

    bool arr[200];
    for (int i = 0; i < 200; i++){
        arr[i] = true;
    }
    
    mpz_t mpz_val;
    mpz_init(mpz_val);
    element_to_mpz(mpz_val, Sc_set_size);
    a = mpz_get_ui(mpz_val);

    for( int i = 1; i < a; i++){
        element_to_mpz(mpz_val, Sc_set[i]);
        b = mpz_get_ui(mpz_val);
        arr[b] = false;
    }

    for(int i = 1; i < set.pp.n; i++){
        if(arr[i] == true){
            element_set(K, sk.K[i]);
            first_Ki = i;
            break;
        }
    }

    for (int i = first_Ki; i < set.pp.n; i++){
        if (arr[i] == true){
            element_mul(K, K, sk.K[i]);
        }
    }
    
    element_pairing(tmp2, ct.C0, K);
    element_div(tmp4, tmp2, tmp3);
    int gap;
    element_set_si(gap_t, 2);
    element_invert(gap_t,gap_t);
    element_to_mpz(mpz_val,gap_t);
    gap = mpz_get_ui(mpz_val);
    printf("反元素: %d\n",gap);
    element_pow_zn(tmp4, tmp4, gap_t);
    element_mul(tmp4, tmp1, tmp4);
    element_div(pt.msg, ct.U, tmp4);
  
    return pt;
}


int main(){
    FILE *fp = fopen("a.param", "r");
    char param[1024];
    size_t count = fread(param, 1, 1024, fp);
    if(! count){
        pbc_die("input error");
        
    }
    pairing_init_set_buf(pairing, param, count);
    SET set;
    SK sk;
    CT ct;
    PT pt;
    set.pp.n = 50;
    int arr[25] = {1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25};
    element_t Sk_set[25];
    element_t Sk_size;
    element_init_Zr(Sk_size, pairing);
    element_set_si(Sk_size, 25);
    for(int i=0; i<25; i++){
        element_init_Zr(Sk_set[i], pairing);
        element_set_si(Sk_set[i], arr[i]);
    }
    int arr2[25] = {26,27,28,29,30,31,32,33,34,35,36,37,38,39,40,41,42,43,44,45,46,47,48,49,50};
    element_t Sc_set[25];
    element_t Sc_size;
    element_init_Zr(Sc_size, pairing);
    element_set_si(Sc_size, 25);
    for(int i=0; i<25; i++){
        element_init_Zr(Sc_set[i], pairing);
        element_set_si(Sc_set[i], arr2[i]);
    }
    start = clock();
    set = setup(set.pp.n);
    end = clock();
    printf("setup花了: %f \n",((double) (end - start)) / CLOCKS_PER_SEC);
    start = clock();
    sk = keygen(set, Sk_set, Sk_size);
    end = clock();
    printf("keygen花了: %f \n",((double) (end - start)) / CLOCKS_PER_SEC);
    element_t message;
    mpz_t mpz_val;
    element_init_GT(message, pairing);
    element_random(message);
    
    element_to_mpz(mpz_val,message);
    unsigned long z;
    z = mpz_get_ui(mpz_val);
    printf("加密前: %lu\n",z);
    start = clock();
    ct = encrypt(set, message, Sc_set, Sc_size);
    end = clock();

    size_t size_ct;
    size_ct = element_length_in_bytes(ct.U) + element_length_in_bytes(ct.C0) + element_length_in_bytes(ct.C1);
    printf("ct大小: %zu bytes\n", size_ct);

    printf("encrypt花了: %f \n",((double) (end - start)) / CLOCKS_PER_SEC);
    start = clock();
    pt = decrypt(set, ct, sk, Sc_set, Sc_size, Sk_set, Sk_size);
    end = clock();
    printf("decrypt花了: %f \n",((double) (end - start)) / CLOCKS_PER_SEC);
    element_to_mpz(mpz_val, pt.msg);
    z = mpz_get_ui(mpz_val);
    printf("解密後: %lu\n", z);





}