#include <stdio.h> 
#include <stdlib.h> 
#include <stdbool.h>
#include <gmp.h> 
#include <pbc/pbc.h>
#include <time.h>

pairing_t pairing;
clock_t start, end;

typedef struct pp {
  element_t P;
  element_t P_pub;
  char X[100][100];
  int n;
} PP;


typedef struct msk {
  element_t s;
} MSK;


typedef struct set {
    PP pp;
    MSK msk;
} SET;

typedef struct key{
    char id[200][11];
    element_t sk[200];
} KEY;

typedef struct ct{
    element_t C1[100];
    element_t C2[100];
} CT;

typedef struct pt{
    element_t k[200][200];
    element_t msg;
} PT;



SET setup(int n){
    SET set;
    set.pp.n = n;
    element_init_Zr(set.msk.s, pairing);
    element_random(set.msk.s);
    element_init_G1(set.pp.P, pairing);
    element_set1(set.pp.P);
    element_init_G1(set.pp.P_pub, pairing);
    element_mul_zn(set.pp.P_pub,set.pp.P,set.msk.s);
    for(int i=1; i<= set.pp.n; i++){
        for(int j=0; j<=9; j++){
             srand((unsigned int)time(NULL));
             set.pp.X[i][j] = (rand() % 2) ? '1' : '0';
        }
    }

    return set;
}


KEY keygen(SET set, element_t Sk_set[], int k_size, element_t Sc_set[], int c_size){
    KEY key;
    bool arr[200] = {false};
    mpz_t mpz_val;
    mpz_init(mpz_val);
    element_t tmp_sk;
    element_init_G1(tmp_sk, pairing);
    int a;
    int b;
    char tmp;
    size_t size_key = 0;
    for(int i=0; i< c_size; i++){
        element_to_mpz(mpz_val, Sc_set[i]);
        a = mpz_get_ui(mpz_val);
        arr[a] = true;
    }
    for(int i=0; i< k_size; i++){
        element_to_mpz(mpz_val,Sk_set[i]);
        b = mpz_get_ui(mpz_val);
        if(arr[b] == true){
            tmp = '1';
        }
        else{
            tmp = '0';
        }
        for(int j=0; j<=9; j++){
            key.id[i][j] = set.pp.X[i][j];
        }
        key.id[i][10] = tmp;
        element_from_hash(tmp_sk, key.id[i], 11);
        element_init_G1(key.sk[i], pairing);
        element_mul_zn(key.sk[i], tmp_sk, set.msk.s);
        size_key += element_length_in_bytes(key.sk[i]);
    }
    printf("key 大小: %zu bytes\n", size_key);
    
    return key;
}

CT encrypt(SET set, KEY key, element_t Sc_set[], int c_size, element_t M){
    CT ct;
    element_t k;
    element_init_GT(k, pairing);
    element_random(k);
    int a;
    bool arr[200] = {false};
    element_t r;
    element_init_Zr(r, pairing);
    element_t g_id;
    element_init_GT(g_id, pairing);
    mpz_t mpz_val;
    mpz_init(mpz_val);
    size_t size_ct = 0;
    for(int i=0; i< c_size; i++){
        element_to_mpz(mpz_val, Sc_set[i]);
        a = mpz_get_ui(mpz_val);
        
        arr[a] = true;

    }
    char id_2[200][11];
    char tmp;
   
    for(int i=1; i<= set.pp.n; i++){
        if(arr[i] == true){
            tmp = '0';
        }
        else{
            tmp = '1';
        }
        for(int j=0; j<=9; j++){
            id_2[i][j] = key.id[i][j];
        }
        id_2[i][10] = tmp;
        element_t tmp_sk;
        element_init_G1(tmp_sk, pairing);
        element_init_G1(ct.C1[i], pairing);
        element_mul_zn(ct.C1[i], set.pp.P, r);
        element_init_GT(ct.C2[i], pairing);
        element_from_hash(tmp_sk, key.id[i], 11);
        element_pairing(ct.C2[i],tmp_sk,set.pp.P_pub);
        element_pow_zn(ct.C2[i], ct.C2[i], r);
        element_clear(tmp_sk);
        element_mul(ct.C2[i], ct.C2[i], k);    
        size_ct += element_length_in_bytes(ct.C1[i]);
        size_ct += element_length_in_bytes(ct.C2[i]);
        
    }
    element_init_GT(ct.C1[0], pairing);
    element_init_GT(ct.C2[0], pairing);
    element_mul(ct.C1[0], k, M);
    element_mul(ct.C2[0], k, M);
    size_ct += element_length_in_bytes(ct.C1[0]);
    size_ct += element_length_in_bytes(ct.C2[0]);
    printf("ct 大小: %zu bytes\n", size_ct);

     return ct;
}

PT decrypt(SET set, CT ct, KEY key, element_t Sk_set[], int k_size, element_t M){
    PT pt;
    mpz_t mpz_val;
    mpz_init(mpz_val);
    element_init_GT(pt.msg, pairing);
    for(int i=1; i <= set.pp.n; i++){
        for(int j=0; j < k_size; j++){
            element_t tmp;
            element_init_GT(pt.k[i][j], pairing);
            element_init_GT(tmp, pairing);
            element_pairing(tmp, key.sk[j], ct.C1[i]);
            element_mul(pt.k[i][j], ct.C2[i], pt.k[i][j]);
            element_t tmp2;
            element_init_GT(tmp2, pairing);
            element_mul(tmp2, pt.k[i][j], M); //這裡有問題
           
            if(element_cmp(ct.C2[0],tmp2) ==0){
                element_mul(pt.msg, ct.C1[0], pt.k[i][j]);
                return pt;
            }
            element_clear(tmp);
            element_clear(tmp2);
        }
    }
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
  KEY sk;
  CT ct;
  PT pt;
  set.pp.n = 50;
  int arr[25] = {1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25};
  element_t Sk_set[25];
  int k_size = 25;
  for(int i=0; i<25; i++){
    element_init_Zr(Sk_set[i], pairing);
    element_set_si(Sk_set[i], arr[i]);
  }
  int arr2[25] = {26,27,28,29,30,31,32,33,34,35,36,37,38,39,40,41,42,43,44,45,46,47,48,49,50};
  element_t Sc_set[25];
  int c_size = 25;
  for(int i=0; i<25; i++){
    element_init_Zr(Sc_set[i], pairing);
    element_set_si(Sc_set[i], arr2[i]);
  }
  start = clock();
  set = setup(set.pp.n);
  end = clock();
  printf("setup花了: %f \n",((double) (end - start)) / CLOCKS_PER_SEC);
  start = clock();
  sk = keygen(set, Sk_set, 25, Sc_set, 25);
  end = clock();
  printf("keygen花了: %f \n",((double) (end - start)) / CLOCKS_PER_SEC);
  element_t message;
  mpz_t mpz_val;
  mpz_init(mpz_val);
  element_init_GT(message, pairing);
  element_random(message);
  element_to_mpz(mpz_val,message);
  unsigned long z;
  z = mpz_get_ui(mpz_val);
  printf("加密前: %lu\n",z);
  start = clock();
  ct = encrypt(set, sk, Sc_set, c_size, message);
  end = clock();
  printf("encrypt花了: %f \n",((double) (end - start)) / CLOCKS_PER_SEC);
  start = clock();
  pt = decrypt(set, ct, sk, Sk_set, k_size, message);
  end = clock();
  printf("decrypt花了: %f \n",((double) (end - start)) / CLOCKS_PER_SEC);
  element_to_mpz(mpz_val, pt.msg);
  z = mpz_get_ui(mpz_val);
  printf("解密後: %lu\n", z);


    

    return 0;
}