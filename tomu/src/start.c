#include <stdint.h>
#include <stdbool.h>

extern unsigned int __etext, __data_start__, __data_end__, __bss_start__, __bss_end__, __stack;
volatile uint32_t msTicks = 0;

// call run from tomu.fort
extern void run();

_Noreturn void Reset_Handler(void)
{
  unsigned int *src = &__etext;
  unsigned int *dst = &__data_start__;

  while (dst < &__data_end__)
    *dst++ = *src++;

  for (dst = &__bss_start__; dst < &__bss_end__; dst++)
    *dst = 0;

  run();

  while (1)
    __asm__ volatile ("WFI");
}

_Noreturn void Default_Handler(void)
{
  while (1);
}

void delay(uint32_t dlyTicks)
{
  uint32_t curTicks;
  curTicks = msTicks;
  while ((msTicks - curTicks) < dlyTicks);
}

void SysTick_Handler()
{
  msTicks++;
}

void __aeabi_unwind_cpp_pr0(void){}

__attribute__((section(".isr_vector"),used)) static void *vectors[] = {
  (void *)&__stack,
  (void *)&Reset_Handler,      // Reset Handler
  (void *)&Default_Handler,    // NMI Handler
  (void *)&Default_Handler,    // Hard Fault Handler
  (void *)&Default_Handler,    // MPU Fault Handler
  (void *)&Default_Handler,    // Bus Fault Handler
  (void *)&Default_Handler,    // Usage Fault Handler
  0,                           // Reserved
  0,                           // Reserved
  0,                           // Reserved
  0,                           // Reserved
  (void *)&Default_Handler,    // SVCall Handler
  (void *)&Default_Handler,    // Debug Monitor Handler
  0,                           // Reserved
  (void *)&Default_Handler,    // PendSV Handler
  (void *)&SysTick_Handler,    // SysTick Handler
};
