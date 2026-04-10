import { defineConfig } from 'vite';

export default defineConfig({
  // Relative base so JS/CSS work on GitHub Pages project sites (/repo/) and custom domains
  base: './',
  server: {
    port: 3000,
    open: true,
    hmr: {
      overlay: true
    }
  },
  build: {
    outDir: 'dist',
    sourcemap: true
  }
});


