
/buildcache/cargo-target/zeebra-632/study/after:     file format elf64-x86-64


Disassembly of section .text:

0000000000142f40 <<criterion::bencher::Bencher>::iter::<zeebra::fields::prime_field_256::PrimeFieldElement256<zeebra::fields::prime_field_256::Bn254FrModulus>, pow_strategy::bench_small_exponent_sites<zeebra::fields::prime_field_256::PrimeFieldElement256<zeebra::fields::prime_field_256::Bn254FrModulus>>::{closure#2}::{closure#0}>>:
  142f40:	55                   	push   %rbp
  142f41:	41 57                	push   %r15
  142f43:	41 56                	push   %r14
  142f45:	41 55                	push   %r13
  142f47:	41 54                	push   %r12
  142f49:	53                   	push   %rbx
  142f4a:	48 81 ec 18 01 00 00 	sub    $0x118,%rsp
  142f51:	48 89 8c 24 e8 00 00 	mov    %rcx,0xe8(%rsp)
  142f58:	00 
  142f59:	48 89 94 24 e0 00 00 	mov    %rdx,0xe0(%rsp)
  142f60:	00 
  142f61:	48 89 b4 24 d8 00 00 	mov    %rsi,0xd8(%rsp)
  142f68:	00 
  142f69:	48 89 fb             	mov    %rdi,%rbx
  142f6c:	c6 47 30 01          	movb   $0x1,0x30(%rdi)
  142f70:	bf 01 00 00 00       	mov    $0x1,%edi
  142f75:	e8 96 11 1f 00       	call   334110 <<std::sys::pal::unix::time::Timespec>::now>
  142f7a:	48 89 84 24 c8 00 00 	mov    %rax,0xc8(%rsp)
  142f81:	00 
  142f82:	89 54 24 3c          	mov    %edx,0x3c(%rsp)
  142f86:	bf 01 00 00 00       	mov    $0x1,%edi
  142f8b:	e8 80 11 1f 00       	call   334110 <<std::sys::pal::unix::time::Timespec>::now>
  142f90:	48 89 84 24 c0 00 00 	mov    %rax,0xc0(%rsp)
  142f97:	00 
  142f98:	89 54 24 38          	mov    %edx,0x38(%rsp)
  142f9c:	48 89 9c 24 d0 00 00 	mov    %rbx,0xd0(%rsp)
  142fa3:	00 
  142fa4:	4c 8b 7b 28          	mov    0x28(%rbx),%r15
  142fa8:	4d 85 ff             	test   %r15,%r15
  142fab:	0f 84 c0 04 00 00    	je     143471 <<criterion::bencher::Bencher>::iter::<zeebra::fields::prime_field_256::PrimeFieldElement256<zeebra::fields::prime_field_256::Bn254FrModulus>, pow_strategy::bench_small_exponent_sites<zeebra::fields::prime_field_256::PrimeFieldElement256<zeebra::fields::prime_field_256::Bn254FrModulus>>::{closure#2}::{closure#0}>+0x531>
  142fb1:	4c 8d 6c 24 60       	lea    0x60(%rsp),%r13
  142fb6:	4c 8d b4 24 f0 00 00 	lea    0xf0(%rsp),%r14
  142fbd:	00 
  142fbe:	eb 65                	jmp    143025 <<criterion::bencher::Bencher>::iter::<zeebra::fields::prime_field_256::PrimeFieldElement256<zeebra::fields::prime_field_256::Bn254FrModulus>, pow_strategy::bench_small_exponent_sites<zeebra::fields::prime_field_256::PrimeFieldElement256<zeebra::fields::prime_field_256::Bn254FrModulus>>::{closure#2}::{closure#0}>+0xe5>
  142fc0:	48 8d 9c 24 a0 00 00 	lea    0xa0(%rsp),%rbx
  142fc7:	00 
  142fc8:	48 89 df             	mov    %rbx,%rdi
  142fcb:	4c 89 e6             	mov    %r12,%rsi
  142fce:	4c 89 e2             	mov    %r12,%rdx
  142fd1:	c5 f8 77             	vzeroupper
  142fd4:	e8 47 51 ff ff       	call   138120 <<&zeebra::fields::prime_field_256::PrimeFieldElement256<zeebra::fields::prime_field_256::Bn254FrModulus> as core::ops::arith::Mul>::mul>
  142fd9:	4c 89 ef             	mov    %r13,%rdi
  142fdc:	48 89 de             	mov    %rbx,%rsi
  142fdf:	48 89 da             	mov    %rbx,%rdx
  142fe2:	c5 f8 77             	vzeroupper
  142fe5:	e8 36 51 ff ff       	call   138120 <<&zeebra::fields::prime_field_256::PrimeFieldElement256<zeebra::fields::prime_field_256::Bn254FrModulus> as core::ops::arith::Mul>::mul>
  142fea:	4c 89 f7             	mov    %r14,%rdi
  142fed:	48 89 e6             	mov    %rsp,%rsi
  142ff0:	4c 89 ea             	mov    %r13,%rdx
  142ff3:	c5 f8 77             	vzeroupper
  142ff6:	e8 25 51 ff ff       	call   138120 <<&zeebra::fields::prime_field_256::PrimeFieldElement256<zeebra::fields::prime_field_256::Bn254FrModulus> as core::ops::arith::Mul>::mul>
  142ffb:	c5 fc 10 84 24 f0 00 	vmovups 0xf0(%rsp),%ymm0
  143002:	00 00 
  143004:	c5 fc 11 04 24       	vmovups %ymm0,(%rsp)
  143009:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
  14300e:	48 8b 44 24 10       	mov    0x10(%rsp),%rax
  143013:	48 8b 04 24          	mov    (%rsp),%rax
  143017:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
  14301c:	49 ff cf             	dec    %r15
  14301f:	0f 84 4c 04 00 00    	je     143471 <<criterion::bencher::Bencher>::iter::<zeebra::fields::prime_field_256::PrimeFieldElement256<zeebra::fields::prime_field_256::Bn254FrModulus>, pow_strategy::bench_small_exponent_sites<zeebra::fields::prime_field_256::PrimeFieldElement256<zeebra::fields::prime_field_256::Bn254FrModulus>>::{closure#2}::{closure#0}>+0x531>
  143025:	48 8b 84 24 d8 00 00 	mov    0xd8(%rsp),%rax
  14302c:	00 
  14302d:	48 89 04 24          	mov    %rax,(%rsp)
  143031:	48 8b 2c 24          	mov    (%rsp),%rbp
  143035:	48 8b 84 24 e0 00 00 	mov    0xe0(%rsp),%rax
  14303c:	00 
  14303d:	48 89 04 24          	mov    %rax,(%rsp)
  143041:	48 8b 84 24 e8 00 00 	mov    0xe8(%rsp),%rax
  143048:	00 
  143049:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
  14304e:	4c 8b 24 24          	mov    (%rsp),%r12
  143052:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
  143057:	48 89 04 24          	mov    %rax,(%rsp)
  14305b:	48 83 f8 04          	cmp    $0x4,%rax
  14305f:	0f 85 e8 04 00 00    	jne    14354d <<criterion::bencher::Bencher>::iter::<zeebra::fields::prime_field_256::PrimeFieldElement256<zeebra::fields::prime_field_256::Bn254FrModulus>, pow_strategy::bench_small_exponent_sites<zeebra::fields::prime_field_256::PrimeFieldElement256<zeebra::fields::prime_field_256::Bn254FrModulus>>::{closure#2}::{closure#0}>+0x60d>
  143065:	c5 fc 10 05 73 30 f8 	vmovups -0x7cf8d(%rip),%ymm0        # c60e0 <.Lanon.e112a8a297db4a9ed05071c05ad3da9c.394>
  14306c:	ff 
  14306d:	c5 fc 11 84 24 f0 00 	vmovups %ymm0,0xf0(%rsp)
  143074:	00 00 
  143076:	c5 fc 11 04 24       	vmovups %ymm0,(%rsp)
  14307b:	48 89 6c 24 20       	mov    %rbp,0x20(%rsp)
  143080:	4c 89 64 24 28       	mov    %r12,0x28(%rsp)
  143085:	8b 45 00             	mov    0x0(%rbp),%eax
  143088:	48 83 f8 05          	cmp    $0x5,%rax
  14308c:	0f 87 af 01 00 00    	ja     143241 <<criterion::bencher::Bencher>::iter::<zeebra::fields::prime_field_256::PrimeFieldElement256<zeebra::fields::prime_field_256::Bn254FrModulus>, pow_strategy::bench_small_exponent_sites<zeebra::fields::prime_field_256::PrimeFieldElement256<zeebra::fields::prime_field_256::Bn254FrModulus>>::{closure#2}::{closure#0}>+0x301>
  143092:	48 8d 0d 5b f6 f2 ff 	lea    -0xd09a5(%rip),%rcx        # 726f4 <GCC_except_table2673+0x408>
  143099:	48 63 04 81          	movslq (%rcx,%rax,4),%rax
  14309d:	48 01 c8             	add    %rcx,%rax
  1430a0:	ff e0                	jmp    *%rax
  1430a2:	c5 fc 10 05 36 30 f8 	vmovups -0x7cfca(%rip),%ymm0        # c60e0 <.Lanon.e112a8a297db4a9ed05071c05ad3da9c.394>
  1430a9:	ff 
  1430aa:	c5 fc 11 44 24 60    	vmovups %ymm0,0x60(%rsp)
  1430b0:	e9 8c 00 00 00       	jmp    143141 <<criterion::bencher::Bencher>::iter::<zeebra::fields::prime_field_256::PrimeFieldElement256<zeebra::fields::prime_field_256::Bn254FrModulus>, pow_strategy::bench_small_exponent_sites<zeebra::fields::prime_field_256::PrimeFieldElement256<zeebra::fields::prime_field_256::Bn254FrModulus>>::{closure#2}::{closure#0}>+0x201>
  1430b5:	48 8d 9c 24 a0 00 00 	lea    0xa0(%rsp),%rbx
  1430bc:	00 
  1430bd:	48 89 df             	mov    %rbx,%rdi
  1430c0:	4c 89 e6             	mov    %r12,%rsi
  1430c3:	4c 89 e2             	mov    %r12,%rdx
  1430c6:	c5 f8 77             	vzeroupper
  1430c9:	e8 52 50 ff ff       	call   138120 <<&zeebra::fields::prime_field_256::PrimeFieldElement256<zeebra::fields::prime_field_256::Bn254FrModulus> as core::ops::arith::Mul>::mul>
  1430ce:	4c 89 ef             	mov    %r13,%rdi
  1430d1:	48 89 de             	mov    %rbx,%rsi
  1430d4:	48 89 da             	mov    %rbx,%rdx
  1430d7:	eb 60                	jmp    143139 <<criterion::bencher::Bencher>::iter::<zeebra::fields::prime_field_256::PrimeFieldElement256<zeebra::fields::prime_field_256::Bn254FrModulus>, pow_strategy::bench_small_exponent_sites<zeebra::fields::prime_field_256::PrimeFieldElement256<zeebra::fields::prime_field_256::Bn254FrModulus>>::{closure#2}::{closure#0}>+0x1f9>
  1430d9:	4c 89 ef             	mov    %r13,%rdi
  1430dc:	4c 89 e6             	mov    %r12,%rsi
  1430df:	eb 55                	jmp    143136 <<criterion::bencher::Bencher>::iter::<zeebra::fields::prime_field_256::PrimeFieldElement256<zeebra::fields::prime_field_256::Bn254FrModulus>, pow_strategy::bench_small_exponent_sites<zeebra::fields::prime_field_256::PrimeFieldElement256<zeebra::fields::prime_field_256::Bn254FrModulus>>::{closure#2}::{closure#0}>+0x1f6>
  1430e1:	48 8d 9c 24 80 00 00 	lea    0x80(%rsp),%rbx
  1430e8:	00 
  1430e9:	48 89 df             	mov    %rbx,%rdi
  1430ec:	4c 89 e6             	mov    %r12,%rsi
  1430ef:	4c 89 e2             	mov    %r12,%rdx
  1430f2:	eb 34                	jmp    143128 <<criterion::bencher::Bencher>::iter::<zeebra::fields::prime_field_256::PrimeFieldElement256<zeebra::fields::prime_field_256::Bn254FrModulus>, pow_strategy::bench_small_exponent_sites<zeebra::fields::prime_field_256::PrimeFieldElement256<zeebra::fields::prime_field_256::Bn254FrModulus>>::{closure#2}::{closure#0}>+0x1e8>
  1430f4:	c4 c1 7c 10 04 24    	vmovups (%r12),%ymm0
  1430fa:	c5 fc 11 44 24 60    	vmovups %ymm0,0x60(%rsp)
  143100:	eb 3f                	jmp    143141 <<criterion::bencher::Bencher>::iter::<zeebra::fields::prime_field_256::PrimeFieldElement256<zeebra::fields::prime_field_256::Bn254FrModulus>, pow_strategy::bench_small_exponent_sites<zeebra::fields::prime_field_256::PrimeFieldElement256<zeebra::fields::prime_field_256::Bn254FrModulus>>::{closure#2}::{closure#0}>+0x201>
  143102:	48 8d 7c 24 40       	lea    0x40(%rsp),%rdi
  143107:	4c 89 e6             	mov    %r12,%rsi
  14310a:	4c 89 e2             	mov    %r12,%rdx
  14310d:	c5 f8 77             	vzeroupper
  143110:	e8 0b 50 ff ff       	call   138120 <<&zeebra::fields::prime_field_256::PrimeFieldElement256<zeebra::fields::prime_field_256::Bn254FrModulus> as core::ops::arith::Mul>::mul>
  143115:	48 8d 9c 24 80 00 00 	lea    0x80(%rsp),%rbx
  14311c:	00 
  14311d:	48 89 df             	mov    %rbx,%rdi
  143120:	48 8d 54 24 40       	lea    0x40(%rsp),%rdx
  143125:	48 89 d6             	mov    %rdx,%rsi
  143128:	c5 f8 77             	vzeroupper
  14312b:	e8 f0 4f ff ff       	call   138120 <<&zeebra::fields::prime_field_256::PrimeFieldElement256<zeebra::fields::prime_field_256::Bn254FrModulus> as core::ops::arith::Mul>::mul>
  143130:	4c 89 ef             	mov    %r13,%rdi
  143133:	48 89 de             	mov    %rbx,%rsi
  143136:	4c 89 e2             	mov    %r12,%rdx
  143139:	c5 f8 77             	vzeroupper
  14313c:	e8 df 4f ff ff       	call   138120 <<&zeebra::fields::prime_field_256::PrimeFieldElement256<zeebra::fields::prime_field_256::Bn254FrModulus> as core::ops::arith::Mul>::mul>
  143141:	4c 89 f3             	mov    %r14,%rbx
  143144:	4c 89 f7             	mov    %r14,%rdi
  143147:	48 89 e6             	mov    %rsp,%rsi
  14314a:	4c 89 ea             	mov    %r13,%rdx
  14314d:	c5 f8 77             	vzeroupper
  143150:	e8 cb 4f ff ff       	call   138120 <<&zeebra::fields::prime_field_256::PrimeFieldElement256<zeebra::fields::prime_field_256::Bn254FrModulus> as core::ops::arith::Mul>::mul>
  143155:	c5 fc 10 84 24 f0 00 	vmovups 0xf0(%rsp),%ymm0
  14315c:	00 00 
  14315e:	c5 fc 11 04 24       	vmovups %ymm0,(%rsp)
  143163:	48 8d 45 04          	lea    0x4(%rbp),%rax
  143167:	4d 8d 74 24 20       	lea    0x20(%r12),%r14
  14316c:	48 89 44 24 20       	mov    %rax,0x20(%rsp)
  143171:	4c 89 74 24 28       	mov    %r14,0x28(%rsp)
  143176:	8b 45 04             	mov    0x4(%rbp),%eax
  143179:	48 83 f8 05          	cmp    $0x5,%rax
  14317d:	0f 87 d5 00 00 00    	ja     143258 <<criterion::bencher::Bencher>::iter::<zeebra::fields::prime_field_256::PrimeFieldElement256<zeebra::fields::prime_field_256::Bn254FrModulus>, pow_strategy::bench_small_exponent_sites<zeebra::fields::prime_field_256::PrimeFieldElement256<zeebra::fields::prime_field_256::Bn254FrModulus>>::{closure#2}::{closure#0}>+0x318>
  143183:	48 8d 0d 82 f5 f2 ff 	lea    -0xd0a7e(%rip),%rcx        # 7270c <GCC_except_table2673+0x420>
  14318a:	48 63 04 81          	movslq (%rcx,%rax,4),%rax
  14318e:	48 01 c8             	add    %rcx,%rax
  143191:	ff e0                	jmp    *%rax
  143193:	c5 fc 10 05 45 2f f8 	vmovups -0x7d0bb(%rip),%ymm0        # c60e0 <.Lanon.e112a8a297db4a9ed05071c05ad3da9c.394>
  14319a:	ff 
  14319b:	c5 fc 11 44 24 60    	vmovups %ymm0,0x60(%rsp)
  1431a1:	e9 ca 00 00 00       	jmp    143270 <<criterion::bencher::Bencher>::iter::<zeebra::fields::prime_field_256::PrimeFieldElement256<zeebra::fields::prime_field_256::Bn254FrModulus>, pow_strategy::bench_small_exponent_sites<zeebra::fields::prime_field_256::PrimeFieldElement256<zeebra::fields::prime_field_256::Bn254FrModulus>>::{closure#2}::{closure#0}>+0x330>
  1431a6:	4c 8d ac 24 a0 00 00 	lea    0xa0(%rsp),%r13
  1431ad:	00 
  1431ae:	4c 89 ef             	mov    %r13,%rdi
  1431b1:	4c 89 f6             	mov    %r14,%rsi
  1431b4:	4c 89 f2             	mov    %r14,%rdx
  1431b7:	c5 f8 77             	vzeroupper
  1431ba:	e8 61 4f ff ff       	call   138120 <<&zeebra::fields::prime_field_256::PrimeFieldElement256<zeebra::fields::prime_field_256::Bn254FrModulus> as core::ops::arith::Mul>::mul>
  1431bf:	48 8d 7c 24 60       	lea    0x60(%rsp),%rdi
  1431c4:	4c 89 ee             	mov    %r13,%rsi
  1431c7:	4c 89 ea             	mov    %r13,%rdx
  1431ca:	4c 8d 6c 24 60       	lea    0x60(%rsp),%r13
  1431cf:	e8 4c 4f ff ff       	call   138120 <<&zeebra::fields::prime_field_256::PrimeFieldElement256<zeebra::fields::prime_field_256::Bn254FrModulus> as core::ops::arith::Mul>::mul>
  1431d4:	e9 97 00 00 00       	jmp    143270 <<criterion::bencher::Bencher>::iter::<zeebra::fields::prime_field_256::PrimeFieldElement256<zeebra::fields::prime_field_256::Bn254FrModulus>, pow_strategy::bench_small_exponent_sites<zeebra::fields::prime_field_256::PrimeFieldElement256<zeebra::fields::prime_field_256::Bn254FrModulus>>::{closure#2}::{closure#0}>+0x330>
  1431d9:	4c 89 ef             	mov    %r13,%rdi
  1431dc:	4c 89 f6             	mov    %r14,%rsi
  1431df:	eb 53                	jmp    143234 <<criterion::bencher::Bencher>::iter::<zeebra::fields::prime_field_256::PrimeFieldElement256<zeebra::fields::prime_field_256::Bn254FrModulus>, pow_strategy::bench_small_exponent_sites<zeebra::fields::prime_field_256::PrimeFieldElement256<zeebra::fields::prime_field_256::Bn254FrModulus>>::{closure#2}::{closure#0}>+0x2f4>
  1431e1:	48 8d bc 24 80 00 00 	lea    0x80(%rsp),%rdi
  1431e8:	00 
  1431e9:	4c 89 f6             	mov    %r14,%rsi
  1431ec:	4c 89 f2             	mov    %r14,%rdx
  1431ef:	eb 30                	jmp    143221 <<criterion::bencher::Bencher>::iter::<zeebra::fields::prime_field_256::PrimeFieldElement256<zeebra::fields::prime_field_256::Bn254FrModulus>, pow_strategy::bench_small_exponent_sites<zeebra::fields::prime_field_256::PrimeFieldElement256<zeebra::fields::prime_field_256::Bn254FrModulus>>::{closure#2}::{closure#0}>+0x2e1>
  1431f1:	c4 c1 7c 10 06       	vmovups (%r14),%ymm0
  1431f6:	c5 fc 11 44 24 60    	vmovups %ymm0,0x60(%rsp)
  1431fc:	eb 72                	jmp    143270 <<criterion::bencher::Bencher>::iter::<zeebra::fields::prime_field_256::PrimeFieldElement256<zeebra::fields::prime_field_256::Bn254FrModulus>, pow_strategy::bench_small_exponent_sites<zeebra::fields::prime_field_256::PrimeFieldElement256<zeebra::fields::prime_field_256::Bn254FrModulus>>::{closure#2}::{closure#0}>+0x330>
  1431fe:	48 8d 7c 24 40       	lea    0x40(%rsp),%rdi
  143203:	4c 89 f6             	mov    %r14,%rsi
  143206:	4c 89 f2             	mov    %r14,%rdx
  143209:	c5 f8 77             	vzeroupper
  14320c:	e8 0f 4f ff ff       	call   138120 <<&zeebra::fields::prime_field_256::PrimeFieldElement256<zeebra::fields::prime_field_256::Bn254FrModulus> as core::ops::arith::Mul>::mul>
  143211:	48 8d bc 24 80 00 00 	lea    0x80(%rsp),%rdi
  143218:	00 
  143219:	48 8d 54 24 40       	lea    0x40(%rsp),%rdx
  14321e:	48 89 d6             	mov    %rdx,%rsi
  143221:	c5 f8 77             	vzeroupper
  143224:	e8 f7 4e ff ff       	call   138120 <<&zeebra::fields::prime_field_256::PrimeFieldElement256<zeebra::fields::prime_field_256::Bn254FrModulus> as core::ops::arith::Mul>::mul>
  143229:	4c 89 ef             	mov    %r13,%rdi
  14322c:	48 8d b4 24 80 00 00 	lea    0x80(%rsp),%rsi
  143233:	00 
  143234:	4c 89 f2             	mov    %r14,%rdx
  143237:	c5 f8 77             	vzeroupper
  14323a:	e8 e1 4e ff ff       	call   138120 <<&zeebra::fields::prime_field_256::PrimeFieldElement256<zeebra::fields::prime_field_256::Bn254FrModulus> as core::ops::arith::Mul>::mul>
  14323f:	eb 2f                	jmp    143270 <<criterion::bencher::Bencher>::iter::<zeebra::fields::prime_field_256::PrimeFieldElement256<zeebra::fields::prime_field_256::Bn254FrModulus>, pow_strategy::bench_small_exponent_sites<zeebra::fields::prime_field_256::PrimeFieldElement256<zeebra::fields::prime_field_256::Bn254FrModulus>>::{closure#2}::{closure#0}>+0x330>
  143241:	89 c2                	mov    %eax,%edx
  143243:	4c 89 ef             	mov    %r13,%rdi
  143246:	4c 89 e6             	mov    %r12,%rsi
  143249:	31 c9                	xor    %ecx,%ecx
  14324b:	c5 f8 77             	vzeroupper
  14324e:	e8 5d b2 ff ff       	call   13e4b0 <<zeebra::fields::prime_field_256::PrimeFieldElement256<zeebra::fields::prime_field_256::Bn254FrModulus> as zeebra::fields::finite_field::FiniteField>::pow>
  143253:	e9 e9 fe ff ff       	jmp    143141 <<criterion::bencher::Bencher>::iter::<zeebra::fields::prime_field_256::PrimeFieldElement256<zeebra::fields::prime_field_256::Bn254FrModulus>, pow_strategy::bench_small_exponent_sites<zeebra::fields::prime_field_256::PrimeFieldElement256<zeebra::fields::prime_field_256::Bn254FrModulus>>::{closure#2}::{closure#0}>+0x201>
  143258:	89 c2                	mov    %eax,%edx
  14325a:	4c 89 ef             	mov    %r13,%rdi
  14325d:	4c 89 f6             	mov    %r14,%rsi
  143260:	31 c9                	xor    %ecx,%ecx
  143262:	c5 f8 77             	vzeroupper
  143265:	e8 46 b2 ff ff       	call   13e4b0 <<zeebra::fields::prime_field_256::PrimeFieldElement256<zeebra::fields::prime_field_256::Bn254FrModulus> as zeebra::fields::finite_field::FiniteField>::pow>
  14326a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
  143270:	49 89 de             	mov    %rbx,%r14
  143273:	48 89 df             	mov    %rbx,%rdi
  143276:	48 89 e6             	mov    %rsp,%rsi
  143279:	4c 89 ea             	mov    %r13,%rdx
  14327c:	c5 f8 77             	vzeroupper
  14327f:	e8 9c 4e ff ff       	call   138120 <<&zeebra::fields::prime_field_256::PrimeFieldElement256<zeebra::fields::prime_field_256::Bn254FrModulus> as core::ops::arith::Mul>::mul>
  143284:	c5 fc 10 84 24 f0 00 	vmovups 0xf0(%rsp),%ymm0
  14328b:	00 00 
  14328d:	c5 fc 11 04 24       	vmovups %ymm0,(%rsp)
  143292:	48 8d 45 08          	lea    0x8(%rbp),%rax
  143296:	49 8d 74 24 40       	lea    0x40(%r12),%rsi
  14329b:	48 89 44 24 20       	mov    %rax,0x20(%rsp)
  1432a0:	48 89 74 24 28       	mov    %rsi,0x28(%rsp)
  1432a5:	8b 45 08             	mov    0x8(%rbp),%eax
  1432a8:	48 83 f8 05          	cmp    $0x5,%rax
  1432ac:	0f 87 ce 00 00 00    	ja     143380 <<criterion::bencher::Bencher>::iter::<zeebra::fields::prime_field_256::PrimeFieldElement256<zeebra::fields::prime_field_256::Bn254FrModulus>, pow_strategy::bench_small_exponent_sites<zeebra::fields::prime_field_256::PrimeFieldElement256<zeebra::fields::prime_field_256::Bn254FrModulus>>::{closure#2}::{closure#0}>+0x440>
  1432b2:	48 8d 0d 6b f4 f2 ff 	lea    -0xd0b95(%rip),%rcx        # 72724 <GCC_except_table2673+0x438>
  1432b9:	48 63 04 81          	movslq (%rcx,%rax,4),%rax
  1432bd:	48 01 c8             	add    %rcx,%rax
  1432c0:	ff e0                	jmp    *%rax
  1432c2:	c5 fc 10 05 16 2e f8 	vmovups -0x7d1ea(%rip),%ymm0        # c60e0 <.Lanon.e112a8a297db4a9ed05071c05ad3da9c.394>
  1432c9:	ff 
  1432ca:	c5 fc 11 44 24 60    	vmovups %ymm0,0x60(%rsp)
  1432d0:	e9 bb 00 00 00       	jmp    143390 <<criterion::bencher::Bencher>::iter::<zeebra::fields::prime_field_256::PrimeFieldElement256<zeebra::fields::prime_field_256::Bn254FrModulus>, pow_strategy::bench_small_exponent_sites<zeebra::fields::prime_field_256::PrimeFieldElement256<zeebra::fields::prime_field_256::Bn254FrModulus>>::{closure#2}::{closure#0}>+0x450>
  1432d5:	48 8d 9c 24 a0 00 00 	lea    0xa0(%rsp),%rbx
  1432dc:	00 
  1432dd:	48 89 df             	mov    %rbx,%rdi
  1432e0:	48 89 f2             	mov    %rsi,%rdx
  1432e3:	c5 f8 77             	vzeroupper
  1432e6:	e8 35 4e ff ff       	call   138120 <<&zeebra::fields::prime_field_256::PrimeFieldElement256<zeebra::fields::prime_field_256::Bn254FrModulus> as core::ops::arith::Mul>::mul>
  1432eb:	4c 89 ef             	mov    %r13,%rdi
  1432ee:	48 89 de             	mov    %rbx,%rsi
  1432f1:	48 89 da             	mov    %rbx,%rdx
  1432f4:	e8 27 4e ff ff       	call   138120 <<&zeebra::fields::prime_field_256::PrimeFieldElement256<zeebra::fields::prime_field_256::Bn254FrModulus> as core::ops::arith::Mul>::mul>
  1432f9:	e9 92 00 00 00       	jmp    143390 <<criterion::bencher::Bencher>::iter::<zeebra::fields::prime_field_256::PrimeFieldElement256<zeebra::fields::prime_field_256::Bn254FrModulus>, pow_strategy::bench_small_exponent_sites<zeebra::fields::prime_field_256::PrimeFieldElement256<zeebra::fields::prime_field_256::Bn254FrModulus>>::{closure#2}::{closure#0}>+0x450>
  1432fe:	4c 89 ef             	mov    %r13,%rdi
  143301:	48 89 f2             	mov    %rsi,%rdx
  143304:	c5 f8 77             	vzeroupper
  143307:	e8 14 4e ff ff       	call   138120 <<&zeebra::fields::prime_field_256::PrimeFieldElement256<zeebra::fields::prime_field_256::Bn254FrModulus> as core::ops::arith::Mul>::mul>
  14330c:	e9 7f 00 00 00       	jmp    143390 <<criterion::bencher::Bencher>::iter::<zeebra::fields::prime_field_256::PrimeFieldElement256<zeebra::fields::prime_field_256::Bn254FrModulus>, pow_strategy::bench_small_exponent_sites<zeebra::fields::prime_field_256::PrimeFieldElement256<zeebra::fields::prime_field_256::Bn254FrModulus>>::{closure#2}::{closure#0}>+0x450>
  143311:	48 8d bc 24 80 00 00 	lea    0x80(%rsp),%rdi
  143318:	00 
  143319:	49 89 f6             	mov    %rsi,%r14
  14331c:	48 89 f2             	mov    %rsi,%rdx
  14331f:	c5 f8 77             	vzeroupper
  143322:	e8 f9 4d ff ff       	call   138120 <<&zeebra::fields::prime_field_256::PrimeFieldElement256<zeebra::fields::prime_field_256::Bn254FrModulus> as core::ops::arith::Mul>::mul>
  143327:	4c 89 ef             	mov    %r13,%rdi
  14332a:	48 8d b4 24 80 00 00 	lea    0x80(%rsp),%rsi
  143331:	00 
  143332:	4c 89 f2             	mov    %r14,%rdx
  143335:	eb 3f                	jmp    143376 <<criterion::bencher::Bencher>::iter::<zeebra::fields::prime_field_256::PrimeFieldElement256<zeebra::fields::prime_field_256::Bn254FrModulus>, pow_strategy::bench_small_exponent_sites<zeebra::fields::prime_field_256::PrimeFieldElement256<zeebra::fields::prime_field_256::Bn254FrModulus>>::{closure#2}::{closure#0}>+0x436>
  143337:	c5 fc 10 06          	vmovups (%rsi),%ymm0
  14333b:	c5 fc 11 44 24 60    	vmovups %ymm0,0x60(%rsp)
  143341:	eb 4d                	jmp    143390 <<criterion::bencher::Bencher>::iter::<zeebra::fields::prime_field_256::PrimeFieldElement256<zeebra::fields::prime_field_256::Bn254FrModulus>, pow_strategy::bench_small_exponent_sites<zeebra::fields::prime_field_256::PrimeFieldElement256<zeebra::fields::prime_field_256::Bn254FrModulus>>::{closure#2}::{closure#0}>+0x450>
  143343:	48 8d 7c 24 40       	lea    0x40(%rsp),%rdi
  143348:	48 89 f2             	mov    %rsi,%rdx
  14334b:	c5 f8 77             	vzeroupper
  14334e:	e8 cd 4d ff ff       	call   138120 <<&zeebra::fields::prime_field_256::PrimeFieldElement256<zeebra::fields::prime_field_256::Bn254FrModulus> as core::ops::arith::Mul>::mul>
  143353:	4c 8d b4 24 80 00 00 	lea    0x80(%rsp),%r14
  14335a:	00 
  14335b:	4c 89 f7             	mov    %r14,%rdi
  14335e:	48 8d 54 24 40       	lea    0x40(%rsp),%rdx
  143363:	48 89 d6             	mov    %rdx,%rsi
  143366:	e8 b5 4d ff ff       	call   138120 <<&zeebra::fields::prime_field_256::PrimeFieldElement256<zeebra::fields::prime_field_256::Bn254FrModulus> as core::ops::arith::Mul>::mul>
  14336b:	4c 89 ef             	mov    %r13,%rdi
  14336e:	4c 89 f6             	mov    %r14,%rsi
  143371:	49 8d 54 24 40       	lea    0x40(%r12),%rdx
  143376:	49 89 de             	mov    %rbx,%r14
  143379:	e8 a2 4d ff ff       	call   138120 <<&zeebra::fields::prime_field_256::PrimeFieldElement256<zeebra::fields::prime_field_256::Bn254FrModulus> as core::ops::arith::Mul>::mul>
  14337e:	eb 10                	jmp    143390 <<criterion::bencher::Bencher>::iter::<zeebra::fields::prime_field_256::PrimeFieldElement256<zeebra::fields::prime_field_256::Bn254FrModulus>, pow_strategy::bench_small_exponent_sites<zeebra::fields::prime_field_256::PrimeFieldElement256<zeebra::fields::prime_field_256::Bn254FrModulus>>::{closure#2}::{closure#0}>+0x450>
  143380:	89 c2                	mov    %eax,%edx
  143382:	4c 89 ef             	mov    %r13,%rdi
  143385:	31 c9                	xor    %ecx,%ecx
  143387:	c5 f8 77             	vzeroupper
  14338a:	e8 21 b1 ff ff       	call   13e4b0 <<zeebra::fields::prime_field_256::PrimeFieldElement256<zeebra::fields::prime_field_256::Bn254FrModulus> as zeebra::fields::finite_field::FiniteField>::pow>
  14338f:	90                   	nop
  143390:	4c 89 f7             	mov    %r14,%rdi
  143393:	48 89 e6             	mov    %rsp,%rsi
  143396:	4c 89 ea             	mov    %r13,%rdx
  143399:	c5 f8 77             	vzeroupper
  14339c:	e8 7f 4d ff ff       	call   138120 <<&zeebra::fields::prime_field_256::PrimeFieldElement256<zeebra::fields::prime_field_256::Bn254FrModulus> as core::ops::arith::Mul>::mul>
  1433a1:	c5 fc 10 84 24 f0 00 	vmovups 0xf0(%rsp),%ymm0
  1433a8:	00 00 
  1433aa:	c5 fc 11 04 24       	vmovups %ymm0,(%rsp)
  1433af:	48 8d 45 0c          	lea    0xc(%rbp),%rax
  1433b3:	49 83 c4 60          	add    $0x60,%r12
  1433b7:	48 89 44 24 20       	mov    %rax,0x20(%rsp)
  1433bc:	4c 89 64 24 28       	mov    %r12,0x28(%rsp)
  1433c1:	8b 45 0c             	mov    0xc(%rbp),%eax
  1433c4:	48 83 f8 05          	cmp    $0x5,%rax
  1433c8:	0f 87 8c 00 00 00    	ja     14345a <<criterion::bencher::Bencher>::iter::<zeebra::fields::prime_field_256::PrimeFieldElement256<zeebra::fields::prime_field_256::Bn254FrModulus>, pow_strategy::bench_small_exponent_sites<zeebra::fields::prime_field_256::PrimeFieldElement256<zeebra::fields::prime_field_256::Bn254FrModulus>>::{closure#2}::{closure#0}>+0x51a>
  1433ce:	48 8d 0d 67 f3 f2 ff 	lea    -0xd0c99(%rip),%rcx        # 7273c <GCC_except_table2673+0x450>
  1433d5:	48 63 04 81          	movslq (%rcx,%rax,4),%rax
  1433d9:	48 01 c8             	add    %rcx,%rax
  1433dc:	ff e0                	jmp    *%rax
  1433de:	c5 fc 10 05 fa 2c f8 	vmovups -0x7d306(%rip),%ymm0        # c60e0 <.Lanon.e112a8a297db4a9ed05071c05ad3da9c.394>
  1433e5:	ff 
  1433e6:	c5 fc 11 44 24 60    	vmovups %ymm0,0x60(%rsp)
  1433ec:	e9 f9 fb ff ff       	jmp    142fea <<criterion::bencher::Bencher>::iter::<zeebra::fields::prime_field_256::PrimeFieldElement256<zeebra::fields::prime_field_256::Bn254FrModulus>, pow_strategy::bench_small_exponent_sites<zeebra::fields::prime_field_256::PrimeFieldElement256<zeebra::fields::prime_field_256::Bn254FrModulus>>::{closure#2}::{closure#0}>+0xaa>
  1433f1:	4c 89 ef             	mov    %r13,%rdi
  1433f4:	4c 89 e6             	mov    %r12,%rsi
  1433f7:	eb 59                	jmp    143452 <<criterion::bencher::Bencher>::iter::<zeebra::fields::prime_field_256::PrimeFieldElement256<zeebra::fields::prime_field_256::Bn254FrModulus>, pow_strategy::bench_small_exponent_sites<zeebra::fields::prime_field_256::PrimeFieldElement256<zeebra::fields::prime_field_256::Bn254FrModulus>>::{closure#2}::{closure#0}>+0x512>
  1433f9:	48 8d 9c 24 80 00 00 	lea    0x80(%rsp),%rbx
  143400:	00 
  143401:	48 89 df             	mov    %rbx,%rdi
  143404:	4c 89 e6             	mov    %r12,%rsi
  143407:	4c 89 e2             	mov    %r12,%rdx
  14340a:	eb 38                	jmp    143444 <<criterion::bencher::Bencher>::iter::<zeebra::fields::prime_field_256::PrimeFieldElement256<zeebra::fields::prime_field_256::Bn254FrModulus>, pow_strategy::bench_small_exponent_sites<zeebra::fields::prime_field_256::PrimeFieldElement256<zeebra::fields::prime_field_256::Bn254FrModulus>>::{closure#2}::{closure#0}>+0x504>
  14340c:	c4 c1 7c 10 04 24    	vmovups (%r12),%ymm0
  143412:	c5 fc 11 44 24 60    	vmovups %ymm0,0x60(%rsp)
  143418:	e9 cd fb ff ff       	jmp    142fea <<criterion::bencher::Bencher>::iter::<zeebra::fields::prime_field_256::PrimeFieldElement256<zeebra::fields::prime_field_256::Bn254FrModulus>, pow_strategy::bench_small_exponent_sites<zeebra::fields::prime_field_256::PrimeFieldElement256<zeebra::fields::prime_field_256::Bn254FrModulus>>::{closure#2}::{closure#0}>+0xaa>
  14341d:	48 8d 6c 24 40       	lea    0x40(%rsp),%rbp
  143422:	48 89 ef             	mov    %rbp,%rdi
  143425:	4c 89 e6             	mov    %r12,%rsi
  143428:	4c 89 e2             	mov    %r12,%rdx
  14342b:	c5 f8 77             	vzeroupper
  14342e:	e8 ed 4c ff ff       	call   138120 <<&zeebra::fields::prime_field_256::PrimeFieldElement256<zeebra::fields::prime_field_256::Bn254FrModulus> as core::ops::arith::Mul>::mul>
  143433:	48 8d 9c 24 80 00 00 	lea    0x80(%rsp),%rbx
  14343a:	00 
  14343b:	48 89 df             	mov    %rbx,%rdi
  14343e:	48 89 ee             	mov    %rbp,%rsi
  143441:	48 89 ea             	mov    %rbp,%rdx
  143444:	c5 f8 77             	vzeroupper
  143447:	e8 d4 4c ff ff       	call   138120 <<&zeebra::fields::prime_field_256::PrimeFieldElement256<zeebra::fields::prime_field_256::Bn254FrModulus> as core::ops::arith::Mul>::mul>
  14344c:	4c 89 ef             	mov    %r13,%rdi
  14344f:	48 89 de             	mov    %rbx,%rsi
  143452:	4c 89 e2             	mov    %r12,%rdx
  143455:	e9 88 fb ff ff       	jmp    142fe2 <<criterion::bencher::Bencher>::iter::<zeebra::fields::prime_field_256::PrimeFieldElement256<zeebra::fields::prime_field_256::Bn254FrModulus>, pow_strategy::bench_small_exponent_sites<zeebra::fields::prime_field_256::PrimeFieldElement256<zeebra::fields::prime_field_256::Bn254FrModulus>>::{closure#2}::{closure#0}>+0xa2>
  14345a:	89 c2                	mov    %eax,%edx
  14345c:	4c 89 ef             	mov    %r13,%rdi
  14345f:	4c 89 e6             	mov    %r12,%rsi
  143462:	31 c9                	xor    %ecx,%ecx
  143464:	c5 f8 77             	vzeroupper
  143467:	e8 44 b0 ff ff       	call   13e4b0 <<zeebra::fields::prime_field_256::PrimeFieldElement256<zeebra::fields::prime_field_256::Bn254FrModulus> as zeebra::fields::finite_field::FiniteField>::pow>
  14346c:	e9 79 fb ff ff       	jmp    142fea <<criterion::bencher::Bencher>::iter::<zeebra::fields::prime_field_256::PrimeFieldElement256<zeebra::fields::prime_field_256::Bn254FrModulus>, pow_strategy::bench_small_exponent_sites<zeebra::fields::prime_field_256::PrimeFieldElement256<zeebra::fields::prime_field_256::Bn254FrModulus>>::{closure#2}::{closure#0}>+0xaa>
  143471:	bf 01 00 00 00       	mov    $0x1,%edi
  143476:	c5 f8 77             	vzeroupper
  143479:	e8 92 0c 1f 00       	call   334110 <<std::sys::pal::unix::time::Timespec>::now>
  14347e:	48 89 84 24 a0 00 00 	mov    %rax,0xa0(%rsp)
  143485:	00 
  143486:	89 94 24 a8 00 00 00 	mov    %edx,0xa8(%rsp)
  14348d:	48 8b 84 24 c0 00 00 	mov    0xc0(%rsp),%rax
  143494:	00 
  143495:	48 89 44 24 40       	mov    %rax,0x40(%rsp)
  14349a:	8b 44 24 38          	mov    0x38(%rsp),%eax
  14349e:	89 44 24 48          	mov    %eax,0x48(%rsp)
  1434a2:	48 89 e7             	mov    %rsp,%rdi
  1434a5:	48 8d b4 24 a0 00 00 	lea    0xa0(%rsp),%rsi
  1434ac:	00 
  1434ad:	48 8d 54 24 40       	lea    0x40(%rsp),%rdx
  1434b2:	e8 99 0b 1f 00       	call   334050 <<std::sys::pal::unix::time::Timespec>::sub_timespec>
  1434b7:	31 db                	xor    %ebx,%ebx
  1434b9:	80 3c 24 00          	cmpb   $0x0,(%rsp)
  1434bd:	8b 44 24 10          	mov    0x10(%rsp),%eax
  1434c1:	0f 45 c3             	cmovne %ebx,%eax
  1434c4:	48 8b 4c 24 08       	mov    0x8(%rsp),%rcx
  1434c9:	48 0f 45 cb          	cmovne %rbx,%rcx
  1434cd:	4c 8b b4 24 d0 00 00 	mov    0xd0(%rsp),%r14
  1434d4:	00 
  1434d5:	49 89 0e             	mov    %rcx,(%r14)
  1434d8:	41 89 46 08          	mov    %eax,0x8(%r14)
  1434dc:	bf 01 00 00 00       	mov    $0x1,%edi
  1434e1:	e8 2a 0c 1f 00       	call   334110 <<std::sys::pal::unix::time::Timespec>::now>
  1434e6:	48 89 84 24 a0 00 00 	mov    %rax,0xa0(%rsp)
  1434ed:	00 
  1434ee:	89 94 24 a8 00 00 00 	mov    %edx,0xa8(%rsp)
  1434f5:	48 8b 84 24 c8 00 00 	mov    0xc8(%rsp),%rax
  1434fc:	00 
  1434fd:	48 89 44 24 40       	mov    %rax,0x40(%rsp)
  143502:	8b 44 24 3c          	mov    0x3c(%rsp),%eax
  143506:	89 44 24 48          	mov    %eax,0x48(%rsp)
  14350a:	48 89 e7             	mov    %rsp,%rdi
  14350d:	48 8d b4 24 a0 00 00 	lea    0xa0(%rsp),%rsi
  143514:	00 
  143515:	48 8d 54 24 40       	lea    0x40(%rsp),%rdx
  14351a:	e8 31 0b 1f 00       	call   334050 <<std::sys::pal::unix::time::Timespec>::sub_timespec>
  14351f:	80 3c 24 00          	cmpb   $0x0,(%rsp)
  143523:	b8 00 00 00 00       	mov    $0x0,%eax
  143528:	75 09                	jne    143533 <<criterion::bencher::Bencher>::iter::<zeebra::fields::prime_field_256::PrimeFieldElement256<zeebra::fields::prime_field_256::Bn254FrModulus>, pow_strategy::bench_small_exponent_sites<zeebra::fields::prime_field_256::PrimeFieldElement256<zeebra::fields::prime_field_256::Bn254FrModulus>>::{closure#2}::{closure#0}>+0x5f3>
  14352a:	8b 5c 24 10          	mov    0x10(%rsp),%ebx
  14352e:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
  143533:	49 89 46 10          	mov    %rax,0x10(%r14)
  143537:	41 89 5e 18          	mov    %ebx,0x18(%r14)
  14353b:	48 81 c4 18 01 00 00 	add    $0x118,%rsp
  143542:	5b                   	pop    %rbx
  143543:	41 5c                	pop    %r12
  143545:	41 5d                	pop    %r13
  143547:	41 5e                	pop    %r14
  143549:	41 5f                	pop    %r15
  14354b:	5d                   	pop    %rbp
  14354c:	c3                   	ret
  14354d:	48 8d 15 74 7f f8 ff 	lea    -0x7808c(%rip),%rdx        # cb4c8 <.Lanon.e112a8a297db4a9ed05071c05ad3da9c.56>
  143554:	4c 8d 0d 75 2e 21 00 	lea    0x212e75(%rip),%r9        # 3563d0 <__dso_handle+0x340>
  14355b:	48 89 e6             	mov    %rsp,%rsi
  14355e:	31 ff                	xor    %edi,%edi
  143560:	31 c9                	xor    %ecx,%ecx
  143562:	c5 f8 77             	vzeroupper
  143565:	e8 8e 54 09 00       	call   1d89f8 <core::panicking::assert_failed::<usize, usize>>
