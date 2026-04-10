# bullishChat - NIP-17 Private Messaging

A secure, private messaging application built on the Nostr protocol with NIP-17 compliance. This app uses gift-wrapped encryption to ensure your messages remain private and secure.

## Features

- 🔒 **NIP-17 Compliant** - Uses gift-wrapped encryption for maximum privacy
- 🛡️ **Extension-Based Security** - Only supports NIP-07 browser extensions (keys never touch the website)
- ⚡ **Hot Module Replacement (HMR)** - Fast development with instant updates
- 🎨 **Modern UI** - Clean, dark-themed interface optimized for messaging

## Prerequisites

- Node.js 18+ and npm
- A NIP-07 compatible browser extension:
  - [Alby](https://getalby.com) (recommended)
  - [nos2x](https://github.com/fiatjaf/nos2x)
  - [Flamingo](https://www.flamingoapp.com/)
  - [horse](https://github.com/fiatjaf/horse)

## Getting Started

1. **Install dependencies:**
   ```bash
   npm install
   ```

2. **Start the development server:**
   ```bash
   npm run dev
   ```

   The app will open automatically at `http://localhost:3000` with HMR enabled.

3. **Build for production:**
   ```bash
   npm run build
   ```

4. **Preview production build:**
   ```bash
   npm run preview
   ```

## Development

The project uses [Vite](https://vitejs.dev/) for fast development with Hot Module Replacement (HMR). Any changes you make to files in the `src/` directory will automatically update in the browser without a full page reload.

### Project Structure

```
bullishchat/
├── index.html          # Main HTML entry point
├── src/
│   ├── main.js        # Application logic
│   └── styles.css     # All styles
├── package.json       # Dependencies and scripts
├── vite.config.js     # Vite configuration
└── README.md          # This file
```

## How It Works

1. **Connect**: Use your NIP-07 browser extension to connect to a Nostr relay
2. **Start Chat**: Enter a recipient's pubkey (npub or hex format)
3. **Send Messages**: Messages are encrypted using NIP-17 gift-wrapping:
   - Messages are wrapped in multiple layers of encryption
   - Each message uses ephemeral keys for additional security
   - Only the intended recipient can decrypt messages

## Security Notes

- This app **only** supports browser extensions - your private keys never leave your extension
- All messages are encrypted using NIP-44 encryption
- Gift-wrapping ensures metadata privacy
- Ephemeral keys are used for each message

## License

MIT

