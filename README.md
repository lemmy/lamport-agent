# Lamport Agent for GitHub Copilot

A GitHub Copilot agent that translates designs or implementations into precise formal specifications and leverages deterministic tools to verify correctness.

## Overview

As AI generates increasingly more code, the skills required to ensure correctness in large systems will become highly valuable. Lamport mode is named after Leslie Lamport, the Turing Award winner who invented the Paxos consensus algorithm and the TLA+ formal language.

## Features

- 🔍 Formal specification generation from designs and implementations
- ✅ Automated correctness verification using deterministic tools
- 🔧 Integration with TLA+ for temporal logic verification
- 🤖 AI-powered agent mode for enhanced productivity

## Prerequisites

- Visual Studio Code Insider
- TLA+ Extension for VS Code
- Model Context Protocol (MCP) support

## Installation

### 1. Create Lamport Agent

1. Open VS Code and navigate to **Chat: New Mode File**
2. Name the new mode "Lamport"
3. Copy the content from `prompts/Lamport.chatmode.md`
4. Restart VS Code
5. Verify that "Lamport" mode appears in the mode selector

<p align="center">
<img src="https://github.com/user-attachments/assets/b29b20a2-6b77-45de-ba4f-ce77ae3db5d5" alt="Lamport Agent Selection" width="500"/>
</p>

### 2. Setup TLA+ MCP

#### Install TLA+ Extension

<p align="center">
<img src="https://github.com/user-attachments/assets/dfe4a421-ef4b-4d4c-a7ec-d0fb102eca29"  alt="TLA+ Extension" width="600"/>
</p>

#### Enable TLA+ MCP

1. Set a non-zero port in the TLA+ extension settings
2. Restart VS Code

<p align="center">
<img src="https://github.com/user-attachments/assets/96595f2b-976f-447c-976a-58ced96bd0f2"  alt="TLA+ MCP Port Configuration" width="660"/>
</p>

#### Verify TLA+ MCP Setup

Click "Configure Tools..." to confirm TLA+ MCP is available:

<p align="center">
<img src="https://github.com/user-attachments/assets/1ec063ce-bdc0-4bf2-9e42-ff792223d50d" alt="Configure Tools Menu" width="660"/>
<img src="https://github.com/user-attachments/assets/79c97adf-503d-4aa5-971a-d885cbacc09d" alt="TLA+ MCP Configured" width="660"/>
</p>

#### Test the Installation

1. Open `test_mcp/DieHarderInstance.tla`
2. Switch to "Agent" mode
3. Execute the specification

<p align="center">
<img src="https://github.com/user-attachments/assets/168ab204-00c3-468f-8f56-7ae51488a677" alt="Execute TLA+ Specification" width="660"/>
</p>

### 3. Setup Sequential Thinking MCP

For advanced sequential reasoning capabilities, install the Sequential Thinking MCP:

- [Sequential Thinking MCP Documentation](https://github.com/modelcontextprotocol/servers/tree/main/src/sequentialthinking)

## Usage

1. Open a project in VS Code
2. Select "Lamport" mode from the chat interface
3. Define verification scope (e.g., a sample prompt for DeepSeek's 3FS)
4. Lamport mode will generate formal specifications and verify correctness

```
let's formally verify the CRAQ implementation and whether it provides consistency between reads and writes, including during storage target failure and rebuild.
```

## Contributing

Contributions are welcome! Please feel free to submit a Pull Request.

## License

This project is licensed under the MIT License - see the [LICENSE](LICENSE) file for details.

## Acknowledgments

- Leslie Lamport for his pioneering work in formal verification
- The TLA+ community for their tools and support
- Microsoft for VS Code and GitHub Copilot
