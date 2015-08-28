/*  Diffe-Hellman key exchange implementation in C (run two instances to generate session)
 *  Xeon Jan 2015
 *  gcc dh-kex.c -o dh-kex -ggdb -Wall -std=c99 -m64 -lm -lcrypto
 *
 * Alice        |   Bob
 * ---------------------------
 * a = random   |
 * A = g^a%p   --> A
 *             |  b = random
 * B           <-- B = g^b%p
 * s = B^a%p    |  s = A^b%p
 * k = KDF(s)   |  k = KDF(s)
 *
 * g = public (prime) base
 * p = public (prime) modulus
 * a = Alice's private key
 * b = Bob's private key
 * A = Alice's public key
 * B = Bob's public key
 * s = shared secret
 * k = encryption key
 */

#include <stdio.h>
#include <stdlib.h>
#include <unistd.h>
#include <stdbool.h>
#include <string.h>
#include <math.h>
#include <time.h>
#include <limits.h>

#include <sys/socket.h>
#include <arpa/inet.h>

#include <openssl/aes.h>
#include <openssl/rand.h>

#define BUFSIZE 1024
#define HOST 0x0100007f /* 0x0100007f == 127.0.0.1 */
#define PORT (unsigned short) 0xB822 /* 8888 */

#define MAX_PRIME 65000 //Bigger the number the slower the algorithm
#define MAXIMUM_PRIME_NUMBER 341550071728321
#define AES_KEYSIZE 256
#define LFSR(n) {if (n&1) n=((n^0x80000055)>>1)|0x80000000; else n>>=1;}
#define ROT(x,y) (x=(x<<y)|(x>>(32-y)))

#define ISHOST 0 /* debug */

struct Keypair {
	unsigned int g, //public (prime) base
	p, //public (prime) modulus
	s, //shared secret
	a, //private key
	A, //A public key
	B; //B public key
};

struct Crypto {
	unsigned char key[AES_KEYSIZE/8], iv[AES_BLOCK_SIZE];
};

void hexdump(const unsigned char *s, unsigned int length)
{
    for(int n = 0; n < length ; ++n) {
        printf("%02x ", s[n] & 0xFF);
    }
    printf("(total %d bytes)\n", length);
}

/* KEY EXCHANGE FUNCTIONS */
bool check_limit(unsigned long val){

        if(val < LONG_MAX)
                return true;

        return false;
}

/* clean variables after each generated key */
void clean_memory(struct Keypair *kp){

        memset(&kp->g, 0, sizeof kp->g);
        memset(&kp->p, 0, sizeof kp->p);
        memset(&kp->s, 0, sizeof kp->s);
        memset(&kp->a, 0, sizeof kp->a);
        memset(&kp->A, 0, sizeof kp->A);
        memset(&kp->B, 0, sizeof kp->B);

        return;
}

/* use ASM to pull EAX/RAX as seed (ReadTimeStampCounter) */
unsigned int rand_int(unsigned int max){
/*
	long long tmp1 = 0;
	long long tmp2 = 0;

	__asm
	{
		RDTSC;                  // Clock cycles since CPU started
		mov tmp1, rax;
		mov tmp2, rdx;
	}

	static unsigned long rnd = 0x41594c49;
	static unsigned long x   = 0x94c49514;

	LFSR(x); 
	rnd ^= (tmp1*tmp2)^x;
	ROT(rnd,7);

	return (unsigned __int64)GetRTSC() + rnd;
*/
	return rand() % max;
}

/* discrete logarithm problem || eliptic curve discrete logarithm problem */
unsigned int XpowYmodN(unsigned int X, unsigned int Y, unsigned int N){

	unsigned int xyn = 1;

	while (Y){
		if (Y & 1)
		xyn = (xyn * X) % N;
		X = (X * X) % N;
		Y = Y >> 1;
	}

/*	printf("base = %lu, modulus = %d\n", b, N);
	printf("XpowYmodN = %d\n", xyn);
*/
	return xyn;
}

bool isPrime(unsigned int N){

        if(XpowYmodN(2, N-1, N) == 1){
                return true;
        }

        return false;
}

/* Miller-Rabin primality test */
bool witness(unsigned int N, unsigned int i, unsigned int Y, unsigned int X){

	unsigned int x = XpowYmodN(X, Y, N);
	unsigned int y;

	while(i) {
		y = (x * x) % N;
		if (y == 1 && x != 1 && x != N-1)
			return false;
		x = y;
		i--;
	}

	if(y != 1)
		return false;
	return true;
}

bool miller_rabin(unsigned int N){

	if(((!(N & 1)) && N != 2 ) || (N < 2) || (N % 3 == 0 && N != 3)){
		return false;
	}

	if(N <= 3){
		return true;
	}

	unsigned int Y = N / 2;
	unsigned int i = 1;

	while(!(Y & 1)) {
		Y /= 2;
		i++;
	}

	if(N < 1373653){
		return witness(N, i, Y, 2) && witness(N, i, Y, 3);
	}

	if(N < 9080191){
		return witness(N, i, Y, 31) && witness(N, i, Y, 73);
	}

	if(N < 4759123141){
		return witness(N, i, Y, 2) && witness(N, i, Y, 7) && witness(N, i, Y, 61);
	}

	if(N < 1122004669633){
		return witness(N, i, Y, 2) && witness(N, i, Y, 13) && witness(N, i, Y, 23) && witness(N, i, Y, 1662803);
	}

	if(N < 2152302898747){
		return witness(N, i, Y, 2) && witness(N, i, Y, 3) && witness(N, i, Y, 5) && witness(N, i, Y, 7) && witness(N, i, Y, 11);
	}

	if(N < 3474749660383){
		return witness(N, i, Y, 2) && witness(N, i, Y, 3) && witness(N, i, Y, 5) && witness(N, i, Y, 7) && witness(N, i, Y, 11) && witness(N, i, Y, 13);
	}

	return witness(N, i, Y, 2) && witness(N, i, Y, 3) && witness(N, i, Y, 5) && witness(N, i, Y, 7) && witness(N, i, Y, 11) && witness(N, i, Y, 13) && witness(N, i, Y, 17);
}

unsigned int generate_prime(){

        unsigned int p = 0;

        p = rand_int(MAX_PRIME);

	if((p&1) == 0)
		p += 1;

	while(1){
//		printf("Testing #%d\n", p); //test
		if(miller_rabin(p))
			break;
		p += 2;
	}

//	printf("Prime generated: %d\n", p);

	return p;
}

bool exist_PubKey(struct Keypair *kp){
        if (kp->A != 0 && kp->B != 0)
                return true;
        return false;
}

void create_PublicKey(struct Keypair *kp){

//	printf("Caculating public key from server values...\n");

	if(!exist_PubKey(kp)){
		kp->a = generate_prime();
		kp->A = XpowYmodN(kp->g, kp->a, kp->p);
		if(kp->A > MAX_PRIME || kp->A < 2){
		/*      printf("public key was > max g || < 3 \n");*/
			create_PublicKey(kp);
		}
		return;
	}
	printf("Public keys  exist. Not generating new ones!\n");
        return;
}

void create_Keypair(struct Keypair *kp){

//	printf("Generating public key...\n");

	if(!exist_PubKey(kp)){
		clean_memory(kp);
		kp->g = generate_prime();

		while(kp->p < kp->g){ //modulus must be larger than generator
			kp->p = generate_prime();
		}
		if(kp->g < 2 || kp->p < 3){
			create_Keypair(kp);
		}

		kp->a = generate_prime();
		kp->A = XpowYmodN(kp->g, kp->a, kp->p);
		if(kp->A > MAX_PRIME || kp->A < 2){
		/*	printf("public key was > max g || < 3 \n");*/
			create_Keypair(kp);
		}
		return;
	}

	printf("Public keys  exist. Not generating new ones!\n");
	return;
}

/* create shared secret */
void create_SecretKey(struct Keypair *kp){

//	printf("Calculating Secret Key...\n");

	kp->s = XpowYmodN(kp->B, kp->a, kp->p);

	return;
}

/* AES FUNCTIONS */
/* generate symmetric cipher key (AES256) */
void generate_EncryptionKey(struct Crypto *c){

	//generate AES key
	memset(&c->key, 0, sizeof c->key);
	if(!RAND_bytes(c->key, AES_KEYSIZE/8)){
        	perror("AES key generation failed: ");
	}

	/* init vector */
	memset(&c->iv, 0, sizeof c->iv);
        if(!RAND_bytes(c->iv, AES_BLOCK_SIZE)){
		perror("AES iv generation failed: ");
	}

	return;
}

unsigned char * encrypt_AES(unsigned char *string, struct Crypto *c){

	const unsigned int enclen = ((sizeof string + AES_BLOCK_SIZE) / AES_BLOCK_SIZE) * AES_BLOCK_SIZE;
	unsigned char *output = malloc (sizeof (char) * enclen);
	memset(output, 0, enclen);

	AES_KEY ekey;
	AES_set_encrypt_key(c->key, AES_KEYSIZE, &ekey);
	AES_cbc_encrypt(string, output, enclen, &ekey, c->iv, AES_ENCRYPT);

//	hexdump(output, sizeof output);
	return output;
}

unsigned char * decrypt_AES(unsigned char *string, struct Crypto *c){

	const unsigned int declen = ((sizeof string + AES_BLOCK_SIZE) / AES_BLOCK_SIZE) * AES_BLOCK_SIZE;
        unsigned char *output = malloc (sizeof (unsigned char) * declen);
	memset(output, 0, declen);

	AES_KEY dkey;
	AES_set_decrypt_key(c->key, AES_KEYSIZE, &dkey);
	AES_cbc_encrypt(string, output, declen, &dkey, c->iv, AES_DECRYPT);

//	hexdump(output, sizeof output);
	return output;
}

/* remove encryption key from memory on session destroy */
void purge_EncryptionKey(struct Crypto *c){

	memset(&c->key, 0, sizeof c->key);
	memset(&c->iv, 0, sizeof c->iv);
	return;
}

/* NETWORK FUNCTIONS */
void print_keypair(struct Keypair *kp){

        printf("Keypair values: \n");
        printf("g: %d\n", kp->g);
        printf("p: %d\n", kp->p);
        printf("s: %d\n", kp->s);
        printf("a: %d\n", kp->a);
        printf("A: %d\n", kp->A);
        printf("B: %d\n", kp->B);

	return;
}

void print_crypto(struct Crypto *c)
{
        unsigned int i;
	printf("Key:\t");
        for(i = 0; i < sizeof c->key; i++)
                printf("%02x ", c->key[i] & 0xFF);
        printf("(total %lu bytes)\n", sizeof c->key);

	printf("IV:\t");
	for(i = 0; i < sizeof c->iv; i++)
        	printf("%02x ", c->iv[i] & 0xFF);
        printf("(total %lu bytes)\n", sizeof c->iv);
}


int main(int argc, char *argv[]) {

        printf("\n *** Running Diffe-Hellman Key Exchange ***\n\n");

	srand(time(NULL)); //seed rand()

/*	///////////////////////// TEST
	struct Crypto c;

	//test vectors//
        unsigned char plaintext[16] = {0x6b, 0xc1, 0xbe, 0xe2, 0x2e, 0x40, 0x9f, 0x96, 0xe9, 0x3d, 0x7e, 0x11, 0x73, 0x93, 0x17, 0x2a};
        unsigned char ciphertext[16] = {0xf5, 0x8c, 0x4c, 0x04, 0xd6, 0xe5, 0xf1, 0xba, 0x77, 0x9e, 0xab, 0xfb, 0x5f, 0x7b, 0xfb, 0xd6};

	static unsigned char testkey[32] = {0x60, 0x3d, 0xeb, 0x10, 0x15, 0xca, 0x71, 0xbe, 0x2b, 0x73, 0xae, 0xf0, 0x85, 0x7d, 0x77, 0x81,
					0x1f, 0x35, 0x2c, 0x07, 0x3b, 0x61, 0x08, 0xd7, 0x2d, 0x98, 0x10, 0xa3, 0x09, 0x14, 0xdf, 0xf4};
	static unsigned char testiv[16] = {0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08, 0x09, 0x0A, 0x0B, 0x0C, 0x0D, 0x0E, 0x0F};
	memcpy(&c.key, testkey, 32);
	memcpy(&c.iv, testiv, 16);

	print_crypto(&c);

	#define TESTCRYPTO 0

	if(TESTCRYPTO){
		if(memcmp(encrypt_AES(plaintext, &c), ciphertext, 16) == 0){
                	printf("encryption success\n");
        	}
	}
	else {
		if(memcmp(decrypt_AES(ciphertext, &c), plaintext, 16) == 0){
                	printf("decryption success\n");
        	}
	}

	return 0;
*/	////////////////////////

	struct sockaddr_in serv_addr, cli_addr;
        memset(&serv_addr, 0, sizeof serv_addr);
        memset(&cli_addr, 0, sizeof cli_addr);

	serv_addr.sin_family = AF_INET;
        serv_addr.sin_port = PORT;

	struct Crypto c;
	unsigned int sockfd, n, clilen;
	char buf[BUFSIZE], username[20], recipname[20];
	unsigned char *plaintext = malloc(BUFSIZE), *ciphertext = malloc(BUFSIZE);
	memset(&buf, 0, BUFSIZE);
	memset(username, 0, sizeof username);
	memset(recipname, 0, sizeof recipname);

	printf("Username: ");
	fgets(username, 20 - 1, stdin);

	char ishost;
        printf("Wait for connection? (y/n): ");
        scanf("%c", &ishost);

	if(ishost == 'y' || ishost == 'Y' || ISHOST){

		/* host */
		serv_addr.sin_addr.s_addr = htonl(INADDR_ANY);
        	sockfd = socket(PF_INET, SOCK_STREAM, IPPROTO_TCP);

        	if(!sockfd){
        	        perror("socket error: ");
        	        return 1;
        	}

        	if(bind(sockfd, (struct sockaddr *) &serv_addr, sizeof serv_addr)){
        	        perror("bind() failed: ");
        	        return 1;
        	}

        	if(listen(sockfd, 1)){
                	perror("listen() failed: ");
                	return 1;
        	}
        	clilen = sizeof cli_addr;

		printf("Waiting...\n");
                sockfd = accept(sockfd, (struct sockaddr *) &cli_addr, &clilen);

              	recv(sockfd, buf, BUFSIZE, 0);

		if(strncmp(buf, "READY", 5) == 0){

			/* name exchange */
                	n = send(sockfd, username, strlen(username), 0);
			memset(&buf, 0, BUFSIZE);
                	recv(sockfd, buf, BUFSIZE, 0);
                	strncpy(recipname, buf, strlen(buf));

                	struct Keypair kp;
                	clean_memory(&kp);

                	create_Keypair(&kp);

                	printf(" *** Incoming connection from %s ***\n", inet_ntoa(cli_addr.sin_addr));
			printf("Secure conversation with %s\n", recipname);

			memset(&buf, 0, BUFSIZE);
			sprintf(buf, "%d,%d,%d", kp.g, kp.p, kp.A);

			n = send(sockfd, buf, strlen(buf), 0);

			memset(&buf, 0, BUFSIZE);
			recv(sockfd, buf, BUFSIZE, 0);

			kp.B = strtol(buf, NULL, 10);

			create_SecretKey(&kp);
//			print_keypair(&kp); //test

			/* send encrypted AES key */
//			printf("Negotiating symmetric key for encryption...\n");

			generate_EncryptionKey(&c);
//			print_crypto(&c); //test

	                memset(&buf, 0, BUFSIZE);
			memcpy(buf, c.key, AES_KEYSIZE/8);
        	        n = send(sockfd, buf, AES_KEYSIZE/8, 0);//TODO, encrypt key

			memset(&buf, 0, BUFSIZE);
                        memcpy(buf, c.iv, 16);
                        n = send(sockfd, buf, 16, 0);

		        /* clean up memory */
		        clean_memory(&kp);
		}
		else {
			printf("Protocol error.\n");
			return 1;
		}
	}

	else { /* client */
		sockfd = socket(AF_INET, SOCK_STREAM, 0);
		serv_addr.sin_addr.s_addr = HOST;

        	n = connect(sockfd, (struct sockaddr *)&serv_addr, sizeof serv_addr);

		strncpy(buf, "READY", 5);
        	n = send(sockfd, buf, strlen(buf), 0);

		/* name exchange */
		memset(&buf, 0, BUFSIZE);
                recv(sockfd, buf, BUFSIZE, 0);
                strncpy(recipname, buf, strlen(buf));
                n = send(sockfd, username, strlen(username), 0);

		struct Keypair kp;
                clean_memory(&kp);

		printf(" *** Outgoing connection to %s ***\n", inet_ntoa(serv_addr.sin_addr));
		printf("Secure conversation with %s\n", recipname);

		memset(&buf, 0, BUFSIZE);
		n = recv(sockfd, buf, BUFSIZE, 0);

		/* Parse string from buffer (bit hacky)*/
		char *tok = strtok(buf, ",");

		kp.g = strtol(tok, NULL, 10);
		tok = strtok(NULL, ",");
		kp.p = strtol(tok, NULL, 10);
                tok = strtok(NULL, ",");
		kp.B = strtol(tok, NULL, 10);
                tok = strtok(NULL, ",");

		memset(&buf, 0, BUFSIZE);
		sprintf(buf, "%d\n", kp.A);
		n = send(sockfd, buf, strlen(buf), 0);

		create_PublicKey(&kp);
		create_SecretKey(&kp);
//		print_keypair(&kp); //test

		/* receive encrypted AES key */
//		printf("Receving encryption key\n");

		memset(&buf, 0, BUFSIZE);
                n = recv(sockfd, buf, BUFSIZE, 0);

		memcpy(c.key, buf, AES_KEYSIZE/8); //TODO, decrypt key
//		printf("AES KEY: %s", c.key); //test

		memset(&buf, 0, BUFSIZE);
                n = recv(sockfd, buf, BUFSIZE, 0);

                memcpy(c.iv, buf, 16);
//		printf("AES IV: %s", c.iv); //test

	        /* clean up memory */
	        clean_memory(&kp);
	}

	/* chat function */
	while(1){
		memset(&buf, 0, BUFSIZE);
		memset(&plaintext, 0, BUFSIZE);
		memset(&ciphertext, 0, BUFSIZE);
		printf(">: ");
		fgets(buf, BUFSIZE - 200, stdin);
		n = send(sockfd, encrypt_AES((unsigned char *)buf, &c), BUFSIZE, 0); //TODO, fix crypto
		if(n <= 0){
			printf("Failure sending message.\n");
			break;
		}
		else {
			memset(&buf, 0, BUFSIZE);
			n = recv(sockfd, buf, BUFSIZE, 0);
			if( n <= 0 ){
				printf("Connection closed.\n");
				break;
			}
			printf("%s: %s\n", recipname, decrypt_AES((unsigned char *)buf, &c));
		}
	}
	n = close(sockfd);
	if(!n){
		return 0;
	}
	return 1;
}
/* TEST KEYS */
/*	if(XpowYmodN(kp.A, b, kp.p) == XpowYmodN(kp.B, kp.a, kp.p))
 *		printf("\nSECRET KEYS MATCH!\n\n");
 */
