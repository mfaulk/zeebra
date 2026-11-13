
/buildcache/cargo-target/zeebra-632/study/before:     file format elf64-x86-64


Disassembly of section .text:

0000000000142e80 <<criterion::bencher::Bencher>::iter::<zeebra::fields::prime_field_256::PrimeFieldElement256<zeebra::fields::prime_field_256::Bn254FrModulus>, pow_strategy::bench_small_exponent_sites<zeebra::fields::prime_field_256::PrimeFieldElement256<zeebra::fields::prime_field_256::Bn254FrModulus>>::{closure#2}::{closure#0}>>:
  142e80:	55                   	push   %rbp
  142e81:	41 57                	push   %r15
  142e83:	41 56                	push   %r14
  142e85:	41 55                	push   %r13
  142e87:	41 54                	push   %r12
  142e89:	53                   	push   %rbx
  142e8a:	48 81 ec b8 00 00 00 	sub    $0xb8,%rsp
  142e91:	48 89 8c 24 90 00 00 	mov    %rcx,0x90(%rsp)
  142e98:	00 
  142e99:	48 89 94 24 88 00 00 	mov    %rdx,0x88(%rsp)
  142ea0:	00 
  142ea1:	48 89 b4 24 80 00 00 	mov    %rsi,0x80(%rsp)
  142ea8:	00 
  142ea9:	48 89 fb             	mov    %rdi,%rbx
  142eac:	c6 47 30 01          	movb   $0x1,0x30(%rdi)
  142eb0:	bf 01 00 00 00       	mov    $0x1,%edi
  142eb5:	e8 66 0b 1f 00       	call   333a20 <<std::sys::pal::unix::time::Timespec>::now>
  142eba:	48 89 44 24 70       	mov    %rax,0x70(%rsp)
  142ebf:	89 54 24 3c          	mov    %edx,0x3c(%rsp)
  142ec3:	bf 01 00 00 00       	mov    $0x1,%edi
  142ec8:	e8 53 0b 1f 00       	call   333a20 <<std::sys::pal::unix::time::Timespec>::now>
  142ecd:	48 89 44 24 68       	mov    %rax,0x68(%rsp)
  142ed2:	89 54 24 38          	mov    %edx,0x38(%rsp)
  142ed6:	48 89 5c 24 78       	mov    %rbx,0x78(%rsp)
  142edb:	4c 8b 63 28          	mov    0x28(%rbx),%r12
  142edf:	4d 85 e4             	test   %r12,%r12
  142ee2:	0f 84 74 01 00 00    	je     14305c <<criterion::bencher::Bencher>::iter::<zeebra::fields::prime_field_256::PrimeFieldElement256<zeebra::fields::prime_field_256::Bn254FrModulus>, pow_strategy::bench_small_exponent_sites<zeebra::fields::prime_field_256::PrimeFieldElement256<zeebra::fields::prime_field_256::Bn254FrModulus>>::{closure#2}::{closure#0}>+0x1dc>
  142ee8:	4c 8d ac 24 98 00 00 	lea    0x98(%rsp),%r13
  142eef:	00 
  142ef0:	48 8d 6c 24 40       	lea    0x40(%rsp),%rbp
  142ef5:	48 89 e3             	mov    %rsp,%rbx
  142ef8:	0f 1f 84 00 00 00 00 	nopl   0x0(%rax,%rax,1)
  142eff:	00 
  142f00:	48 8b 84 24 80 00 00 	mov    0x80(%rsp),%rax
  142f07:	00 
  142f08:	48 89 04 24          	mov    %rax,(%rsp)
  142f0c:	4c 8b 34 24          	mov    (%rsp),%r14
  142f10:	48 8b 84 24 88 00 00 	mov    0x88(%rsp),%rax
  142f17:	00 
  142f18:	48 89 04 24          	mov    %rax,(%rsp)
  142f1c:	48 8b 84 24 90 00 00 	mov    0x90(%rsp),%rax
  142f23:	00 
  142f24:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
  142f29:	4c 8b 3c 24          	mov    (%rsp),%r15
  142f2d:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
  142f32:	48 89 04 24          	mov    %rax,(%rsp)
  142f36:	48 83 f8 04          	cmp    $0x4,%rax
  142f3a:	0f 85 ef 01 00 00    	jne    14312f <<criterion::bencher::Bencher>::iter::<zeebra::fields::prime_field_256::PrimeFieldElement256<zeebra::fields::prime_field_256::Bn254FrModulus>, pow_strategy::bench_small_exponent_sites<zeebra::fields::prime_field_256::PrimeFieldElement256<zeebra::fields::prime_field_256::Bn254FrModulus>>::{closure#2}::{closure#0}>+0x2af>
  142f40:	c5 fc 10 05 d8 30 f8 	vmovups -0x7cf28(%rip),%ymm0        # c6020 <.Lanon.e112a8a297db4a9ed05071c05ad3da9c.394>
  142f47:	ff 
  142f48:	c5 fc 11 44 24 40    	vmovups %ymm0,0x40(%rsp)
  142f4e:	c5 fc 11 04 24       	vmovups %ymm0,(%rsp)
  142f53:	4c 89 74 24 20       	mov    %r14,0x20(%rsp)
  142f58:	4c 89 7c 24 28       	mov    %r15,0x28(%rsp)
  142f5d:	41 8b 16             	mov    (%r14),%edx
  142f60:	4c 89 ef             	mov    %r13,%rdi
  142f63:	4c 89 fe             	mov    %r15,%rsi
  142f66:	31 c9                	xor    %ecx,%ecx
  142f68:	c5 f8 77             	vzeroupper
  142f6b:	e8 80 b4 ff ff       	call   13e3f0 <<zeebra::fields::prime_field_256::PrimeFieldElement256<zeebra::fields::prime_field_256::Bn254FrModulus> as zeebra::fields::finite_field::FiniteField>::pow>
  142f70:	48 89 ef             	mov    %rbp,%rdi
  142f73:	48 89 de             	mov    %rbx,%rsi
  142f76:	4c 89 ea             	mov    %r13,%rdx
  142f79:	e8 e2 50 ff ff       	call   138060 <<&zeebra::fields::prime_field_256::PrimeFieldElement256<zeebra::fields::prime_field_256::Bn254FrModulus> as core::ops::arith::Mul>::mul>
  142f7e:	c5 fc 10 44 24 40    	vmovups 0x40(%rsp),%ymm0
  142f84:	c5 fc 11 04 24       	vmovups %ymm0,(%rsp)
  142f89:	49 8d 46 04          	lea    0x4(%r14),%rax
  142f8d:	49 8d 77 20          	lea    0x20(%r15),%rsi
  142f91:	48 89 44 24 20       	mov    %rax,0x20(%rsp)
  142f96:	48 89 74 24 28       	mov    %rsi,0x28(%rsp)
  142f9b:	41 8b 56 04          	mov    0x4(%r14),%edx
  142f9f:	4c 89 ef             	mov    %r13,%rdi
  142fa2:	31 c9                	xor    %ecx,%ecx
  142fa4:	c5 f8 77             	vzeroupper
  142fa7:	e8 44 b4 ff ff       	call   13e3f0 <<zeebra::fields::prime_field_256::PrimeFieldElement256<zeebra::fields::prime_field_256::Bn254FrModulus> as zeebra::fields::finite_field::FiniteField>::pow>
  142fac:	48 89 ef             	mov    %rbp,%rdi
  142faf:	48 89 de             	mov    %rbx,%rsi
  142fb2:	4c 89 ea             	mov    %r13,%rdx
  142fb5:	e8 a6 50 ff ff       	call   138060 <<&zeebra::fields::prime_field_256::PrimeFieldElement256<zeebra::fields::prime_field_256::Bn254FrModulus> as core::ops::arith::Mul>::mul>
  142fba:	c5 fc 10 44 24 40    	vmovups 0x40(%rsp),%ymm0
  142fc0:	c5 fc 11 04 24       	vmovups %ymm0,(%rsp)
  142fc5:	49 8d 46 08          	lea    0x8(%r14),%rax
  142fc9:	49 8d 77 40          	lea    0x40(%r15),%rsi
  142fcd:	48 89 44 24 20       	mov    %rax,0x20(%rsp)
  142fd2:	48 89 74 24 28       	mov    %rsi,0x28(%rsp)
  142fd7:	41 8b 56 08          	mov    0x8(%r14),%edx
  142fdb:	4c 89 ef             	mov    %r13,%rdi
  142fde:	31 c9                	xor    %ecx,%ecx
  142fe0:	c5 f8 77             	vzeroupper
  142fe3:	e8 08 b4 ff ff       	call   13e3f0 <<zeebra::fields::prime_field_256::PrimeFieldElement256<zeebra::fields::prime_field_256::Bn254FrModulus> as zeebra::fields::finite_field::FiniteField>::pow>
  142fe8:	48 89 ef             	mov    %rbp,%rdi
  142feb:	48 89 de             	mov    %rbx,%rsi
  142fee:	4c 89 ea             	mov    %r13,%rdx
  142ff1:	e8 6a 50 ff ff       	call   138060 <<&zeebra::fields::prime_field_256::PrimeFieldElement256<zeebra::fields::prime_field_256::Bn254FrModulus> as core::ops::arith::Mul>::mul>
  142ff6:	c5 fc 10 44 24 40    	vmovups 0x40(%rsp),%ymm0
  142ffc:	c5 fc 11 04 24       	vmovups %ymm0,(%rsp)
  143001:	49 8d 46 0c          	lea    0xc(%r14),%rax
  143005:	49 83 c7 60          	add    $0x60,%r15
  143009:	48 89 44 24 20       	mov    %rax,0x20(%rsp)
  14300e:	4c 89 7c 24 28       	mov    %r15,0x28(%rsp)
  143013:	41 8b 56 0c          	mov    0xc(%r14),%edx
  143017:	4c 89 ef             	mov    %r13,%rdi
  14301a:	4c 89 fe             	mov    %r15,%rsi
  14301d:	31 c9                	xor    %ecx,%ecx
  14301f:	c5 f8 77             	vzeroupper
  143022:	e8 c9 b3 ff ff       	call   13e3f0 <<zeebra::fields::prime_field_256::PrimeFieldElement256<zeebra::fields::prime_field_256::Bn254FrModulus> as zeebra::fields::finite_field::FiniteField>::pow>
  143027:	48 89 ef             	mov    %rbp,%rdi
  14302a:	48 89 de             	mov    %rbx,%rsi
  14302d:	4c 89 ea             	mov    %r13,%rdx
  143030:	e8 2b 50 ff ff       	call   138060 <<&zeebra::fields::prime_field_256::PrimeFieldElement256<zeebra::fields::prime_field_256::Bn254FrModulus> as core::ops::arith::Mul>::mul>
  143035:	c5 fc 10 44 24 40    	vmovups 0x40(%rsp),%ymm0
  14303b:	c5 fc 11 04 24       	vmovups %ymm0,(%rsp)
  143040:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
  143045:	48 8b 44 24 10       	mov    0x10(%rsp),%rax
  14304a:	48 8b 04 24          	mov    (%rsp),%rax
  14304e:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
  143053:	49 ff cc             	dec    %r12
  143056:	0f 85 a4 fe ff ff    	jne    142f00 <<criterion::bencher::Bencher>::iter::<zeebra::fields::prime_field_256::PrimeFieldElement256<zeebra::fields::prime_field_256::Bn254FrModulus>, pow_strategy::bench_small_exponent_sites<zeebra::fields::prime_field_256::PrimeFieldElement256<zeebra::fields::prime_field_256::Bn254FrModulus>>::{closure#2}::{closure#0}>+0x80>
  14305c:	bf 01 00 00 00       	mov    $0x1,%edi
  143061:	c5 f8 77             	vzeroupper
  143064:	e8 b7 09 1f 00       	call   333a20 <<std::sys::pal::unix::time::Timespec>::now>
  143069:	48 89 44 24 40       	mov    %rax,0x40(%rsp)
  14306e:	89 54 24 48          	mov    %edx,0x48(%rsp)
  143072:	48 8b 44 24 68       	mov    0x68(%rsp),%rax
  143077:	48 89 84 24 98 00 00 	mov    %rax,0x98(%rsp)
  14307e:	00 
  14307f:	8b 44 24 38          	mov    0x38(%rsp),%eax
  143083:	89 84 24 a0 00 00 00 	mov    %eax,0xa0(%rsp)
  14308a:	48 89 e7             	mov    %rsp,%rdi
  14308d:	48 8d 74 24 40       	lea    0x40(%rsp),%rsi
  143092:	48 8d 94 24 98 00 00 	lea    0x98(%rsp),%rdx
  143099:	00 
  14309a:	e8 c1 08 1f 00       	call   333960 <<std::sys::pal::unix::time::Timespec>::sub_timespec>
  14309f:	31 db                	xor    %ebx,%ebx
  1430a1:	80 3c 24 00          	cmpb   $0x0,(%rsp)
  1430a5:	8b 44 24 10          	mov    0x10(%rsp),%eax
  1430a9:	0f 45 c3             	cmovne %ebx,%eax
  1430ac:	48 8b 4c 24 08       	mov    0x8(%rsp),%rcx
  1430b1:	48 0f 45 cb          	cmovne %rbx,%rcx
  1430b5:	4c 8b 74 24 78       	mov    0x78(%rsp),%r14
  1430ba:	49 89 0e             	mov    %rcx,(%r14)
  1430bd:	41 89 46 08          	mov    %eax,0x8(%r14)
  1430c1:	bf 01 00 00 00       	mov    $0x1,%edi
  1430c6:	e8 55 09 1f 00       	call   333a20 <<std::sys::pal::unix::time::Timespec>::now>
  1430cb:	48 89 44 24 40       	mov    %rax,0x40(%rsp)
  1430d0:	89 54 24 48          	mov    %edx,0x48(%rsp)
  1430d4:	48 8b 44 24 70       	mov    0x70(%rsp),%rax
  1430d9:	48 89 84 24 98 00 00 	mov    %rax,0x98(%rsp)
  1430e0:	00 
  1430e1:	8b 44 24 3c          	mov    0x3c(%rsp),%eax
  1430e5:	89 84 24 a0 00 00 00 	mov    %eax,0xa0(%rsp)
  1430ec:	48 89 e7             	mov    %rsp,%rdi
  1430ef:	48 8d 74 24 40       	lea    0x40(%rsp),%rsi
  1430f4:	48 8d 94 24 98 00 00 	lea    0x98(%rsp),%rdx
  1430fb:	00 
  1430fc:	e8 5f 08 1f 00       	call   333960 <<std::sys::pal::unix::time::Timespec>::sub_timespec>
  143101:	80 3c 24 00          	cmpb   $0x0,(%rsp)
  143105:	b8 00 00 00 00       	mov    $0x0,%eax
  14310a:	75 09                	jne    143115 <<criterion::bencher::Bencher>::iter::<zeebra::fields::prime_field_256::PrimeFieldElement256<zeebra::fields::prime_field_256::Bn254FrModulus>, pow_strategy::bench_small_exponent_sites<zeebra::fields::prime_field_256::PrimeFieldElement256<zeebra::fields::prime_field_256::Bn254FrModulus>>::{closure#2}::{closure#0}>+0x295>
  14310c:	8b 5c 24 10          	mov    0x10(%rsp),%ebx
  143110:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
  143115:	49 89 46 10          	mov    %rax,0x10(%r14)
  143119:	41 89 5e 18          	mov    %ebx,0x18(%r14)
  14311d:	48 81 c4 b8 00 00 00 	add    $0xb8,%rsp
  143124:	5b                   	pop    %rbx
  143125:	41 5c                	pop    %r12
  143127:	41 5d                	pop    %r13
  143129:	41 5e                	pop    %r14
  14312b:	41 5f                	pop    %r15
  14312d:	5d                   	pop    %rbp
  14312e:	c3                   	ret
  14312f:	48 8d 15 d2 82 f8 ff 	lea    -0x77d2e(%rip),%rdx        # cb408 <.Lanon.e112a8a297db4a9ed05071c05ad3da9c.56>
  143136:	4c 8d 0d a3 2b 21 00 	lea    0x212ba3(%rip),%r9        # 355ce0 <__dso_handle+0x340>
  14313d:	48 89 e6             	mov    %rsp,%rsi
  143140:	31 ff                	xor    %edi,%edi
  143142:	31 c9                	xor    %ecx,%ecx
  143144:	c5 f8 77             	vzeroupper
  143147:	e8 bc 51 09 00       	call   1d8308 <core::panicking::assert_failed::<usize, usize>>
